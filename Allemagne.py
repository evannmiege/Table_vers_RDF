#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from datetime import datetime
import os
import re
import time
import unicodedata

import pandas as pd
import pycountry
from geopy.exc import GeocoderServiceError, GeocoderTimedOut
from geopy.geocoders import Nominatim
from rdflib import BNode, Graph, Literal, Namespace, URIRef
from rdflib.namespace import RDF, RDFS, SKOS, XSD
from event_text_utils import infer_day_of_week_name, infer_source_category_key

# -------------------- CONFIGURATION --------------------
ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
CSV_PATH = "Allemagne/Allemagne.csv"
OUTPUT_TTL = "Allemagne/frontlet_import_output.ttl"
MAPPING_PATH = "Allemagne/mappingAllemagneThesaurusCauseMort.csv"
ROW_LIMIT = None

GEOCODE_TIME_BUDGET_SEC = 30
GEOCODE_MAX_AFTER_BUDGET = 10

# Espaces de noms par defaut
F = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")

# ----------------- Fonctions utilitaires ----------------
def norm(value):
    if value is None:
        return ""
    text = str(value).strip()
    text = unicodedata.normalize("NFKD", text)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = re.sub(r"\s+", " ", text)
    return text.lower()


def is_missing(value):
    if value is None:
        return True
    text = norm(value)
    if text == "":
        return True
    return text in {
        "nan",
        "none",
        "n/a",
        "na",
        "-",
        "unknown",
        "unkonown",
        "unknwon",
        "non connu",
        "non connu(e)",
    }


def slugify(value):
    cleaned = re.sub(r"[^a-z0-9_]+", "_", norm(value))
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    return cleaned or "unknown"


def find_by_label(g, search, props=(RDFS.label, SKOS.prefLabel)):
    if search is None or str(search).strip() == "":
        return None
    s_norm = norm(search)
    for p in props:
        for s, _, o in g.triples((None, p, None)):
            if norm(o) == s_norm:
                return s
    for p in props:
        for s, _, o in g.triples((None, p, None)):
            if s_norm in norm(o):
                return s
    return None


def copy_all_class_hierarchy(g_src, g_dst):
    class_predicates = (RDF.type, RDFS.subClassOf, SKOS.prefLabel, SKOS.definition, RDFS.label)
    class_uris = {
        subject
        for subject in g_src.subjects(RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class"))
        if str(subject).startswith(str(F))
    }
    expanded = set(class_uris)
    for class_uri in list(class_uris):
        for subj, _, _ in g_src.triples((None, RDFS.subClassOf, class_uri)):
            if str(subj).startswith(str(F)):
                expanded.add(subj)

    for class_uri in expanded:
        for predicate in class_predicates:
            for _, _, obj in g_src.triples((class_uri, predicate, None)):
                g_dst.add((class_uri, predicate, obj))


def find_thesaurus_term_by_pref_label(g, label):
    if label is None or str(label).strip() == "":
        return None
    lbl = norm(label)
    for s, _, o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == lbl:
            return s
    for s, _, o in g.triples((None, RDFS.label, None)):
        if norm(o) == lbl:
            return s
    return None


def copy_resource_description(g_src, g_dst, resource_uri, predicates=None):
    if resource_uri is None:
        return
    predicates = predicates or (RDF.type, RDFS.label, RDFS.comment, SKOS.prefLabel, SKOS.broader)
    for predicate in predicates:
        for _, _, obj in g_src.triples((resource_uri, predicate, None)):
            g_dst.add((resource_uri, predicate, obj))


def create_or_get_death_cause_instance(graph, cause_label, thesaurus_uri=None):
    if is_missing(cause_label):
        return None

    cause_uri = DATA["allemagne_DeathCause_" + slugify(cause_label)]
    if (cause_uri, RDF.type, F.DeathCause) not in graph:
        graph.add((cause_uri, RDF.type, F.DeathCause))
        graph.add((cause_uri, RDFS.label, Literal(str(cause_label).strip(), lang="fr")))
    if thesaurus_uri is not None:
        graph.add((cause_uri, SKOS.closeMatch, thesaurus_uri))
    return cause_uri


def create_or_get_death_nature_instance(graph, nature_label, thesaurus_uri=None):
    if is_missing(nature_label):
        return None

    nature_uri = DATA["allemagne_DeathNature_" + slugify(nature_label)]
    if (nature_uri, RDF.type, F.DeathNature) not in graph:
        graph.add((nature_uri, RDF.type, F.DeathNature))
        graph.add((nature_uri, RDFS.label, Literal(str(nature_label).strip(), lang="fr")))
    if thesaurus_uri is not None:
        graph.add((nature_uri, SKOS.closeMatch, thesaurus_uri))
    return nature_uri


def ensure_gender_instances(graph):
    """Create canonical frontlet:Gender instances used by Allemagne output."""
    specs = {
        "genre": {
            "uri": DATA["allemagne_Gender_genre"],
            "label": "genre",
            "match": T.gender,
        },
        "masculin": {
            "uri": DATA["allemagne_Gender_masculin"],
            "label": "masculin",
            "match": T.male,
        },
        "feminin": {
            "uri": DATA["allemagne_Gender_feminin"],
            "label": "féminin",
            "match": T.female,
        },
        "inconnu": {
            "uri": DATA["allemagne_Gender_inconnu"],
            "label": "inconnu",
            "match": T.gender_unknown,
        },
        "autre": {
            "uri": DATA["allemagne_Gender_autre"],
            "label": "autre",
            "match": T.gender_other,
        },
    }

    for spec in specs.values():
        g_uri = spec["uri"]
        if (g_uri, RDF.type, F.Gender) not in graph:
            graph.add((g_uri, RDF.type, F.Gender))
            graph.add((g_uri, RDFS.label, Literal(spec["label"], lang="fr")))
            graph.add((g_uri, SKOS.closeMatch, spec["match"]))

    return {
        "male": specs["masculin"]["uri"],
        "female": specs["feminin"]["uri"],
        "unknown": specs["inconnu"]["uri"],
        "other": specs["autre"]["uri"],
        "generic": specs["genre"]["uri"],
    }


def parse_int_value(value):
    if is_missing(value):
        return None
    text = str(value).strip().replace(",", ".")
    match = re.search(r"[-+]?\d+(?:\.\d+)?", text)
    if not match:
        return None
    try:
        return int(float(match.group(0)))
    except Exception:
        return None


def parse_age_values(value):
    """Return all valid ages found in a cell, preserving order (e.g. '33 e 39 anni' -> [33, 39])."""
    if is_missing(value):
        return []
    text = norm(value)
    values = []
    for token in re.findall(r"\b\d{1,3}\b", text):
        try:
            age = int(token)
        except Exception:
            continue
        if 0 <= age <= 120:
            values.append(age)
    return values


def infer_age_values_from_text(*values):
    """Extract age hints from free text across EN/FR/DE/IT/ES/PL variants."""
    text = "\n".join(str(v) for v in values if v is not None)
    if text.strip() == "":
        return []

    patterns = [
        r"\b(\d{1,3})\s*[- ]?(?:year(?:s)?(?: old)?|yo)\b",
        r"\b(\d{1,3})\s*ans\b",
        r"\b(\d{1,3})\s*anni\b",
        r"\b(\d{1,3})\s*a(?:n|ñ)os\b",
        r"\b(\d{1,3})\s*jahre?\b",
        r"\b(\d{1,3})\s*[- ]?jahrig\b",
        r"\b(\d{1,3})\s*lat\b",
        r"\baged\s*(\d{1,3})\b",
        r"\bage\s*(\d{1,3})\b",
        r"\bw wieku\s*(\d{1,3})\b",
        r"\bim alter von\s*(\d{1,3})\b",
    ]

    out = []
    for pattern in patterns:
        for match in re.findall(pattern, norm(text), flags=re.IGNORECASE):
            try:
                age = int(match)
            except Exception:
                continue
            if 0 <= age <= 120 and age not in out:
                out.append(age)
    return out


def parse_sex_value(value):
    text = norm(value)
    if text == "":
        return None, 1

    m = re.match(r"^(\d+)\s*([mf])$", text)
    if m:
        count = max(1, int(m.group(1)))
        return ("male" if m.group(2) == "m" else "female"), count

    female_tokens = {"f", "female", "femme", "woman", "donna"}
    male_tokens = {"m", "male", "homme", "man", "uomo"}

    if any(tok in text for tok in female_tokens):
        return "female", 1
    if any(tok in text for tok in male_tokens):
        return "male", 1

    return None, 1


def split_country_values(raw_value):
    if is_missing(raw_value):
        return []
    pieces = re.split(r";|,|/|\||\band\b|\bor\b|\be\b|\bet\b", str(raw_value), flags=re.IGNORECASE)
    return [p.strip() for p in pieces if p and p.strip()]


def ensure_country_node(graph, country_code_or_name):
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    cc = None
    sval = re.sub(r"[^A-Za-z0-9]", "", val).upper()

    try:
        if re.fullmatch(r"[A-Z]{2}", sval):
            cc = pycountry.countries.get(alpha_2=sval)
        elif re.fullmatch(r"[A-Z]{3}", sval):
            cc = pycountry.countries.get(alpha_3=sval)
    except Exception:
        cc = None

    if cc is None:
        try:
            matches = pycountry.countries.search_fuzzy(val)
            if matches:
                cc = matches[0]
        except Exception:
            cc = None

    if cc is not None:
        iso3 = getattr(cc, "alpha_3", None)
        if not iso3:
            return None
        uri = DATA["allemagne_Country_" + iso3.upper()]
        if (uri, None, None) not in graph:
            graph.add((uri, RDF.type, F.Country))
            graph.add((uri, RDFS.label, Literal(getattr(cc, "name", val), lang="en")))
            graph.add((uri, F.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            graph.add((uri, F.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            graph.add((uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return uri

    fallback = find_by_label(graph, val)
    if fallback:
        return fallback

    slug = slugify(val)
    if slug in {"", "nan", "none", "unknown"}:
        return None
    uri = DATA["allemagne_Country_" + slug]
    if (uri, None, None) not in graph:
        graph.add((uri, RDF.type, F.Country))
        graph.add((uri, RDFS.label, Literal(val)))
    return uri


def ensure_country_nodes(graph, raw_value):
    nodes = []
    for candidate in split_country_values(raw_value):
        cnode = ensure_country_node(graph, candidate)
        if cnode:
            nodes.append(cnode)
    return nodes


MONTH_MAP = {
    "january": "01",
    "february": "02",
    "march": "03",
    "april": "04",
    "may": "05",
    "june": "06",
    "july": "07",
    "august": "08",
    "september": "09",
    "october": "10",
    "november": "11",
    "december": "12",
    "gennaio": "01",
    "febbraio": "02",
    "marzo": "03",
    "aprile": "04",
    "maggio": "05",
    "giugno": "06",
    "luglio": "07",
    "agosto": "08",
    "settembre": "09",
    "ottobre": "10",
    "novembre": "11",
    "dicembre": "12",
}


def parse_date_to_iso(raw_value):
    if is_missing(raw_value):
        return None

    text = str(raw_value).strip()
    text = re.sub(r"\s+", " ", text)
    text = text.replace(" ,", ",")

    direct_formats = [
        "%Y-%m-%d",
        "%d.%m.%Y",
        "%d.%m.%y",
        "%d/%m/%Y",
        "%d/%m/%y",
        "%d-%m-%Y",
        "%d-%m-%y",
        "%B %d, %Y",
        "%b %d, %Y",
    ]

    cleaned = text.rstrip(".").strip()
    for fmt in direct_formats:
        try:
            return datetime.strptime(cleaned, fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue

    # dd.mm.yyyy with optional spaces and trailing punctuation in larger text
    m = re.search(r"(\d{1,2})\s*[./-]\s*(\d{1,2})\s*[./-]\s*(\d{2,4})", cleaned)
    if m:
        day = int(m.group(1))
        month = int(m.group(2))
        year = int(m.group(3))
        if year < 100:
            year = 2000 + year
        try:
            return datetime(year, month, day).strftime("%Y-%m-%d")
        except ValueError:
            pass

    # Month DD, YYYY (english/italian), possibly embedded in larger text
    month_regex = "|".join(sorted(MONTH_MAP.keys(), key=len, reverse=True))
    m = re.search(r"(" + month_regex + r")\s+(\d{1,2}),\s*(\d{4})", norm(cleaned), flags=re.IGNORECASE)
    if m:
        month_token = m.group(1).lower()
        month = int(MONTH_MAP[month_token])
        day = int(m.group(2))
        year = int(m.group(3))
        try:
            return datetime(year, month, day).strftime("%Y-%m-%d")
        except ValueError:
            pass

    return None


def parse_birth_year(raw_value):
    if is_missing(raw_value):
        return "unknown", None

    text = norm(raw_value)
    if text in {"unknown", "unkonown", "unknwon"}:
        return "unknown", None

    # Prefer a four-digit year found anywhere in the cell.
    year_match = re.search(r"\b(18\d{2}|19\d{2}|20\d{2}|21\d{2})\b", text)
    if year_match:
        year = year_match.group(1)
        return year, Literal(year, datatype=XSD.gYear)

    return str(raw_value).strip(), Literal(str(raw_value).strip())


def is_suspicious_coordinate(lat, lon):
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return True

    if lon == -99 and lat == -99:
        return True
    if abs(lon) > 180 or abs(lat) > 90:
        return True
    if lat > 70:
        return True
    if -14 < lat < -12 and 43 < lon < 45:
        return True
    return False


def parse_coordinates_from_location(raw_location):
    if is_missing(raw_location):
        return None, None

    text = str(raw_location).strip().replace(";", " ")
    m = re.search(r"([-+]?\d{1,2}(?:\.\d+)?)\s*,\s*([-+]?\d{1,3}(?:\.\d+)?)", text)
    if not m:
        return None, None

    try:
        first = float(m.group(1))
        second = float(m.group(2))
    except Exception:
        return None, None

    # Assume first is latitude, second is longitude.
    lat, lon = first, second
    if is_suspicious_coordinate(lat, lon):
        return None, None
    return lat, lon


def parse_coordinates_from_fields(raw_latitude, raw_longitude):
    if is_missing(raw_latitude) or is_missing(raw_longitude):
        return None, None
    try:
        lat = float(str(raw_latitude).strip().replace(",", "."))
        lon = float(str(raw_longitude).strip().replace(",", "."))
    except Exception:
        return None, None
    if is_suspicious_coordinate(lat, lon):
        return None, None
    return lat, lon


def details_indicate_inhumation(details_text):
    if is_missing(details_text):
        return False
    text = norm(details_text)
    positive = [
        "burial",
        "buried",
        "burried",
        "cemetery",
        "grave",
        "inhum",
        "interment",
        "sepolt",
        "sepolto",
        "sepolta",
        "sepoltura",
    ]
    return any(token in text for token in positive)


def collect_text_values(row, names):
    """Collect non-empty text values from multiple candidate columns."""
    out = []
    for name in names:
        if name not in row.index:
            continue
        val = row.get(name, "")
        if not is_missing(val):
            out.append(str(val).strip())
    return out


def build_additional_event_specs(g_ref):
    """Map IndividualEvent subclasses to keyword hints in DE/FR/EN text."""
    def _cls(label, fallback):
        return find_by_label(g_ref, label) or fallback

    return [
        {
            "name": "Inhumation",
            "class_uri": _cls("Inhumation", F.Inhumation),
            "post_mortem": True,
            "patterns": [
                r"\bburial\b", r"\bburied\b", r"\bcemetery\b", r"\bgrave\b",
                r"\binhumat", r"\binterment\b", r"\bbeerdig", r"\bgrab\b", r"\bfriedhof\b",
                r"\bsepolt",
            ],
        },
        {
            "name": "CorpseAnalysis",
            "class_uri": _cls("Corpse analysis", F.CorpseAnalysis),
            "post_mortem": True,
            "patterns": [
                r"\bautops", r"\bpost[-\s]?mortem\b", r"\bforensic\b",
                r"\bcorpse analysis\b", r"\banalyse du corps\b", r"\bobduktion\b",
                r"\bleichenschau\b", r"\bnecrops",
            ],
        },
        {
            "name": "CorpseRepatriation",
            "class_uri": _cls("Corpse repatriation", F.CorpseRepatriation),
            "post_mortem": True,
            "patterns": [
                r"\brepatriat", r"\btransferred.*body\b", r"\bbody.*transferred\b",
                r"\bbody returned\b", r"\brapatriement du corps\b", r"\bruckfuhr", r"\bruckfuehr",
                r"\buberfuhr", r"\bueberfuehr",
            ],
        },
        {
            "name": "Control",
            "class_uri": _cls("Control", F.Control),
            "post_mortem": False,
            "patterns": [
                r"\bcontrol\b", r"\bcontrole\b", r"\bkontroll", r"\bpolice check\b",
                r"\bidentity check\b", r"\bcheckpoint\b",
            ],
        },
        {
            "name": "Trace",
            "class_uri": _cls("Trace", F.Trace),
            "post_mortem": False,
            "patterns": [
                r"\btrace\b", r"\bpiste\b", r"\bfootprint\b", r"\bpersonal belongings\b",
                r"\bbelongings found\b", r"\babandoned object\b", r"\bobjets? (?:abandonn|laiss)",
                r"\bspur\b", r"\bgegenstand\b",
            ],
        },
        {
            "name": "Testimony",
            "class_uri": _cls("Testimony", F.Testimony),
            "post_mortem": False,
            "patterns": [
                r"\btestimon", r"\bwitness\b", r"\beyewitness\b", r"\btemoign", r"\bzeugen?\b",
            ],
        },
        {
            "name": "Call",
            "class_uri": _cls("Call", F.Call),
            "post_mortem": False,
            "patterns": [
                r"\bcall(?:ed|ing)?\b", r"\bphone\b", r"\btelephone\b", r"\bappel\b",
                r"\bcalled his\b", r"\bcalled her\b", r"\banruf\b", r"\btelefon",
            ],
        },
        {
            "name": "Conversation",
            "class_uri": _cls("Conversation", F.Conversation),
            "post_mortem": False,
            "patterns": [
                r"\bconversation\b", r"\bdiscuss(?:ed|ion)?\b", r"\btalk(?:ed|ing)?\b",
                r"\bspoke\b", r"\binterview\b", r"\bentretien\b", r"\bdiskut", r"\bgesprach\b", r"\bgespraech\b",
            ],
        },
    ]


def detect_additional_event_specs(text_chunks, specs):
    if not text_chunks:
        return []
    text = norm("\n".join(text_chunks))
    found = []
    for spec in specs:
        for pattern in spec["patterns"]:
            if re.search(pattern, text, flags=re.IGNORECASE):
                found.append(spec)
                break
    return found


def detect_transport_from_cause(cause_text, extra_text=""):
    texts = [norm(cause_text or ""), norm(extra_text or "")]
    text = " ".join(t for t in texts if t)
    if not text.strip():
        return None
    patterns = [
        ("train", ["train", "rail", "locomotive", "zug", "bahn", "eisenbahn", "gueterwagen", "gueterzug", "treno"]),
        ("car", ["car", "vehicle", "auto", "automobile", "pkw", "kraftfahrzeug", "voiture"]),
        ("truck", ["truck", "lorry", "camion", "lkw", "lastwagen", "laster"]),
        ("bus", ["bus", "coach", "autobus", "reisebus"]),
        ("motorbike", ["motorbike", "motorcycle", "moto", "scooter", "motorrad"]),
        ("bicycle", ["bicycle", "bike", "cyclist", "fahrrad"]),
        ("boat", ["boat", "ship", "vessel", "ferry", "raft", "dinghy", "boot", "schiff", "schlauchboot", "barca", "patera"]),
        ("plane", ["plane", "aircraft", "airplane", "helicopter", "flugzeug", "hubschrauber"]),
        ("foot", ["foot", "walking", "fuss", "zu fuss", "fußganger", "laufen"]),
    ]
    for transport, keywords in patterns:
        if any(keyword in text for keyword in keywords):
            return transport
    return None


def load_death_cause_thesaurus(graph):
    cause_map = {}
    for cause_uri in graph.subjects(RDF.type, T.DeathCause):
        for label_obj in graph.objects(cause_uri, SKOS.prefLabel):
            if label_obj.language == "fr" or label_obj.language is None:
                label_norm = norm(str(label_obj))
                if label_norm:
                    cause_map[label_norm] = (cause_uri, str(label_obj))
    return cause_map


def load_mapping_csv(mapping_path=MAPPING_PATH):
    mapping_cause = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        return mapping_cause, mapping_nature
    try:
        mdf = pd.read_csv(mapping_path, sep=";", dtype=str)
        cols = list(mdf.columns)
        if len(cols) >= 2:
            left = cols[0]
            right = cols[1]
            nature_col = "Nature" if "Nature" in mdf.columns else None
            for _, row in mdf.iterrows():
                k = norm(row.get(left, ""))
                v = str(row.get(right, "")).strip()
                if k and v:
                    mapping_cause[k] = v
                if nature_col is not None:
                    n = str(row.get(nature_col, "")).strip()
                    if k and n:
                        mapping_nature[k] = n
    except Exception:
        pass
    return mapping_cause, mapping_nature


def match_death_cause(value, mapping_dict, thesaurus_map, nature_mapping):
    if is_missing(value):
        return None, None, None, False

    val_norm = norm(value)
    mapped_label = mapping_dict.get(val_norm)
    mapped_nature = nature_mapping.get(val_norm)
    if mapped_label:
        mapped_norm = norm(mapped_label)
        thes_entry = thesaurus_map.get(mapped_norm)
        if thes_entry:
            uri, thes_label = thes_entry
            return uri, thes_label, mapped_nature, False
        return None, mapped_label, mapped_nature, True

    thes_entry = thesaurus_map.get(val_norm)
    if thes_entry:
        uri, thes_label = thes_entry
        return uri, thes_label, mapped_nature, False

    for lbl, thes_entry in thesaurus_map.items():
        if lbl and lbl in val_norm:
            uri, thes_label = thes_entry
            return uri, thes_label, mapped_nature, False

    val_words = set(re.findall(r"\b\w+\b", val_norm))
    best_uri = None
    best_lbl = None
    best_overlap = 0
    for lbl, thes_entry in thesaurus_map.items():
        uri, thes_label = thes_entry
        lbl_words = set(re.findall(r"\b\w+\b", lbl))
        overlap = len(val_words & lbl_words)
        if overlap > best_overlap and overlap >= 2:
            best_uri = uri
            best_lbl = thes_label
            best_overlap = overlap

    if best_uri:
        return best_uri, best_lbl, mapped_nature, False

    return None, str(value).strip(), mapped_nature, True


def get_value(row, names):
    for name in names:
        if name in row.index:
            value = row.get(name, "")
            if value is not None:
                return value
    return ""


# ---- German number words for summaries_text parsing ----
GERMAN_NUM_WORDS = {
    "ein": 1, "eine": 1, "einen": 1, "einer": 1, "einem": 1,
    "zwei": 2, "drei": 3, "vier": 4, "fünf": 5, "sechs": 6,
    "sieben": 7, "acht": 8, "neun": 9, "zehn": 10, "elf": 11,
    "zwölf": 12, "dreizehn": 13, "vierzehn": 14, "fünfzehn": 15,
    "sechzehn": 16, "siebzehn": 17, "achtzehn": 18, "neunzehn": 19,
    "zwanzig": 20, "einundzwanzig": 21, "zweiundzwanzig": 22,
    "dreiundzwanzig": 23, "vierundzwanzig": 24, "fünfundzwanzig": 25,
    "sechsundzwanzig": 26, "siebenundzwanzig": 27, "achtundzwanzig": 28,
    "neunundzwanzig": 29, "dreißig": 30, "vierzig": 40, "fünfzig": 50,
    "sechzig": 60, "siebzig": 70, "achtzig": 80, "neunzig": 90,
    "hundert": 100,
}
_GERMAN_NUM_RE = re.compile(
    r"\b(" + "|".join(sorted(GERMAN_NUM_WORDS, key=len, reverse=True)) + r")\b",
    re.IGNORECASE,
)

_SUM_DEATH_RE = re.compile(
    r"\b(starb(?:en)?|tötete(?:n)?\s+sich|getötet(?:e[nm]?)?|gestorben"
    r"|ums\s+leben\s+(?:gekommen|kamen)|ertrank(?:en)?|tot\s+aufgefund)\b",
    re.IGNORECASE,
)
_SUM_INJURY_RE = re.compile(
    r"\b(verletzt(?:e[nm]?)?|verletzungen?|erlitten?)\b",
    re.IGNORECASE,
)
_SUM_MISSING_RE = re.compile(
    r"\b(verscholl(?:en)?|vermi(?:ss|ß)t)\b",
    re.IGNORECASE,
)
_SUM_SURVIVED_RE = re.compile(r"\büberlebten?\b", re.IGNORECASE)
_SUM_SUBCOUNT_RE = re.compile(
    r"^\s*(davon|allein|darunter|dabei|darin)\b", re.IGNORECASE
)


def _extract_first_number(text):
    """Return first meaningful number in text as int, or None.
    Skips 4-digit years (1900-2099). Handles German word numbers."""
    m = re.search(r"\b(\d{1,4})\b", text)
    if m:
        val = int(m.group(1))
        if 1900 <= val <= 2099:
            return _extract_first_number(text[m.end():])
        # Ignorer les descripteurs d'age comme "5-Jahrige"
        if re.match(r"-[Jj]ähr", text[m.end():]):
            return _extract_first_number(text[m.end():])
        return val
    m2 = _GERMAN_NUM_RE.search(text)
    if m2:
        return GERMAN_NUM_WORDS.get(m2.group(1).lower())
    return None


def parse_summaries_text_events(text):
    """Parse a German annual summary text.
    Returns {'deaths': int, 'injuries': int, 'missing': int, 'year': int or None}."""
    if not text or str(text).strip() == "":
        return {"deaths": 0, "injuries": 0, "missing": 0, "year": None}

    deaths = 0
    injuries = 0
    missing = 0
    year = None

    ym = re.search(r"\bJahres?\s+(\d{4})\b", text, re.IGNORECASE)
    if ym:
        year = int(ym.group(1))

    for para in re.split(r"\n\n+", text):
        # Split paragraph into sentences at ". " before an uppercase letter or digit.
        sentences = re.split(r"\.\s+(?=[A-ZÄÖÜ0-9])", para)
        for sent in sentences:
            sent = sent.strip()
            if not sent:
                continue
            # Split sentence into clauses at comma and semicolon.
            # Also split at " und " to separate conjoined event descriptions
            # (e.g. "109 verletzt ... und eine Person starb").
            raw_clauses = re.split(r"[,;]", sent)
            clauses = []
            for _rc in raw_clauses:
                clauses.extend(re.split(r"\s+und\s+", _rc))
            last_number = None
            for clause in clauses:
                clause = clause.strip()
                if not clause:
                    continue
                if _SUM_SUBCOUNT_RE.match(clause):
                    continue
                n = _extract_first_number(clause)
                if n is not None and n > 0:
                    last_number = n
                effective_n = last_number
                if effective_n is None:
                    continue
                # Deces: verbe present, sans contexte de survie.
                if _SUM_DEATH_RE.search(clause) and not _SUM_SURVIVED_RE.search(clause):
                    deaths += effective_n
                    last_number = None
                    continue
                # Injury: verbe de blessure present.
                if _SUM_INJURY_RE.search(clause):
                    injuries += effective_n
                    last_number = None
                    continue
                # Missing.
                if _SUM_MISSING_RE.search(clause):
                    missing += effective_n
                    last_number = None

    return {"deaths": deaths, "injuries": injuries, "missing": missing, "year": year}


# ----------------- Chargement des graphes ----------------
g_ref = Graph()
g_ref.parse(ONTO_PATH, format="turtle")
g_ref.parse(THES_PATH, format="turtle")

g = Graph()
g.bind("frontlet", F)
g.bind("frontlet_data", DATA)
g.bind("thes", T)
g.bind("skos", SKOS)
g.bind("rdfs", RDFS)
g.bind("rdf", RDF)
g.bind("geo", GEO)
g.bind("time", TIME)
g.bind("temp", TEMP)

copy_all_class_hierarchy(g_ref, g)

thesaurus_map = load_death_cause_thesaurus(g_ref)
mapping_dict, mapping_nature = load_mapping_csv(MAPPING_PATH)

# -------------------- Lecture du CSV --------------------
encodings_to_try = ["utf-8", "utf-8-sig", "cp1252", "latin-1"]
df = None
used_encoding = None
for _enc in encodings_to_try:
    try:
        df = pd.read_csv(
            CSV_PATH,
            sep=None,
            engine="python",
            dtype=str,
            keep_default_na=False,
            na_values=["", "NaN", "nan"],
            encoding=_enc,
        )
        used_encoding = _enc
        break
    except (UnicodeDecodeError, pd.errors.ParserError):
        continue

if df is None:
    raise RuntimeError(f"Unable to read CSV: {CSV_PATH}")

if ROW_LIMIT is not None and len(df) > ROW_LIMIT:
    df = df.head(ROW_LIMIT).copy()

print(f"CSV loaded ({used_encoding}): {len(df)} rows, {len(df.columns)} columns")

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
SOURCE_CLASS = find_by_label(g_ref, "Source") or F.Source
COLLECTIVE_EVENT_CLASS = find_by_label(g_ref, "Collective event") or F.CollectiveEvent
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death
INHUMATION_CLASS = find_by_label(g_ref, "Inhumation") or F.Inhumation
MISSING_EVENT_CLASS = F.Missing
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or F.Injury

# Garantir que la classe Missing existe et reste alignee avec les evenements individuels.
if (MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_EVENT_CLASS, RDFS.subClassOf, F.IndividualEvent))
    if (MISSING_EVENT_CLASS, RDFS.label, None) not in g:
        g.add((MISSING_EVENT_CLASS, RDFS.label, Literal("Missing", lang="en")))

PROP_hasName = find_by_label(g_ref, "hasName") or F.hasName
PROP_gender = find_by_label(g_ref, "has gender") or F.hasGender
PROP_birthPlace = find_by_label(g_ref, "birth place") or F.birthPlace
PROP_composedOf = find_by_label(g_ref, "composedOf") or F.composedOf
PROP_hasAgeLink = find_by_label(g_ref, "aged") or F.aged
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_hasNarrative = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_group = find_by_label(g_ref, "group") or F.group
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after
PROP_transportType = find_by_label(g_ref, "transport type") or F.transportType
PROP_transportName = find_by_label(g_ref, "transport name") or F.transportName
PROP_numberDead = find_by_label(g_ref, "number dead") or F.numberDead
PROP_numberMissing = find_by_label(g_ref, "number of missing") or F.numberMissing
PROP_totalDeadAndMissing = find_by_label(g_ref, "total dead and missing") or F.totalDeadAndMissing
PROP_yearOfBirth = find_by_label(g_ref, "year of birth") or F.yearOfBirth
DEATH_CAUSE_CLASS = find_by_label(g_ref, "DeathCause") or F.DeathCause

copy_resource_description(g_ref, g, T.Gender)
copy_resource_description(g_ref, g, T.gender)
copy_resource_description(g_ref, g, T.male)
copy_resource_description(g_ref, g, T.female)
copy_resource_description(g_ref, g, T.gender_unknown)
copy_resource_description(g_ref, g, T.gender_other)

GENDER_URIS = ensure_gender_instances(g)
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref)

geolocator = Nominatim(user_agent="frontlet_allemagne_geocoder")
location_geocode_cache = {}
geocode_start_time = time.time()
geocode_after_budget_calls = 0


def geocode_location(location_name, max_retries=2):
    global geocode_after_budget_calls

    if is_missing(location_name):
        return None, None

    location_str = str(location_name).strip()
    key = norm(location_str)
    if key in location_geocode_cache:
        return location_geocode_cache[key]

    elapsed = time.time() - geocode_start_time
    if elapsed > GEOCODE_TIME_BUDGET_SEC and geocode_after_budget_calls >= GEOCODE_MAX_AFTER_BUDGET:
        location_geocode_cache[key] = (None, None)
        return None, None

    if elapsed > GEOCODE_TIME_BUDGET_SEC:
        geocode_after_budget_calls += 1

    for _ in range(max_retries):
        try:
            location = geolocator.geocode(location_str, timeout=8)
            if location:
                lat = float(location.latitude)
                lon = float(location.longitude)
                if not is_suspicious_coordinate(lat, lon):
                    location_geocode_cache[key] = (lat, lon)
                    return lat, lon
            break
        except (GeocoderTimedOut, GeocoderServiceError):
            continue
        except Exception:
            break

    location_geocode_cache[key] = (None, None)
    return None, None


def create_age_node(graph, age_values, row_index, person_index):
    if not age_values:
        return None
    age_num = age_values[min(person_index, len(age_values) - 1)]
    age_uri = DATA[f"allemagne_Age_{row_index + 1}_{person_index + 1}"]
    graph.add((age_uri, RDF.type, F.Age))
    graph.add((age_uri, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    return age_uri


# ------------------- Traitement des lignes ----------------
count_person = 0
count_individual_events = 0
count_death_events = 0
count_missing_events = 0
count_collective_events = 0
count_inhumation_events = 0
count_additional_typed_events = 0
count_sources = 0
count_transports = 0
count_geo_from_csv = 0
count_geocoded = 0
count_geocode_skipped = 0
count_cause_matched = 0
count_cause_from_raw = 0
count_nature_mapped = 0
count_date_from_morgue_taken = 0
count_date_from_brought_to_morgue = 0

created_collective_events = set()
created_transports = set()

for idx, row in df.iterrows():
    row_num = idx + 1

    name_val = get_value(row, ["title"])
    sex_val = get_value(row, ["SEX"])
    birth_val = get_value(row, ["DATE OR YEAR OF BIRTH", "YEAR OF BIRTH"])
    origin_val = get_value(row, ["country_of_origin", "COUNTRY OF ORIGIN"])
    death_date_val = get_value(row, ["date", "DATE OF DEATH or FINDING", "DEATH or FINDING"])
    taken_morgue_val = get_value(row, ["Taken from the morgue by the funeral agency"])
    brought_morgue_val = get_value(row, ["Brought to Morgue"])
    cause_val = get_value(row, ["categories", "CAUSE OF DEATH"])
    details_val = get_value(row, ["narrative_text", "info_text", "DETAILS"])
    location_val = get_value(row, ["location_custom_name", "LOCATION ", "LOCATION"])
    latitude_val = get_value(row, ["latitude"])
    longitude_val = get_value(row, ["longitude"])
    source_url_val = get_value(row, ["href", "SOURCES"])
    sources_text_val = get_value(row, ["sources_text"])
    info_source_val = get_value(row, ["Information Source"]) or sources_text_val or get_value(row, ["title"])
    age_raw_val = get_value(row, ["Age"])
    summary_val = get_value(row, ["summaries_text"])

    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values(row, ["narrative_text", "info_text", "DETAILS"]))
    text_chunks_for_typing.extend(collect_text_values(row, ["title", "sources_text", "source_text", "Information Source"]))
    if not is_missing(summary_val):
        text_chunks_for_typing.append(str(summary_val).strip())

    number_dead = parse_int_value(get_value(row, ["Number Dead"])) or 1
    number_missing = parse_int_value(get_value(row, ["Minimum Estimated Number of Missing"])) or 0
    total_dead_missing = parse_int_value(get_value(row, ["Total Dead and Missing"]))

    normalized_gender, sex_count_hint = parse_sex_value(sex_val)

    # Si SEX indique explicitement "2 M" / "2 F", imposer au moins ce nombre d'evenements deces.
    if number_dead == 0 and number_missing == 0:
        number_dead = max(1, sex_count_hint)
    else:
        number_dead = max(number_dead, sex_count_hint)

    if total_dead_missing is None:
        total_dead_missing = number_dead + number_missing
    total_dead_missing = max(total_dead_missing, number_dead + number_missing, 1)

    # Les victimes restantes hors repartition dead/missing sont considerees comme des deces par defaut.
    assigned = number_dead + number_missing
    if total_dead_missing > assigned:
        number_dead += total_dead_missing - assigned

    victim_total = number_dead + number_missing

    # Resoudre la date d'evenement avec l'ordre de repli demande.
    death_iso = parse_date_to_iso(death_date_val)
    date_comment = None
    if death_iso is None:
        death_iso = parse_date_to_iso(taken_morgue_val)
        if death_iso is not None:
            date_comment = "Taken from the morgue by the funeral agency"
            count_date_from_morgue_taken += 1
    if death_iso is None:
        death_iso = parse_date_to_iso(brought_morgue_val)
        if death_iso is not None:
            date_comment = "Brought to Morgue"
            count_date_from_brought_to_morgue += 1

    birth_literal_text, birth_literal_value = parse_birth_year(birth_val)
    age_values = parse_age_values(age_raw_val)
    if not age_values:
        age_values = infer_age_values_from_text(
            get_value(row, ["title"]),
            get_value(row, ["info_text", "DETAILS"]),
            get_value(row, ["narrative_text"]),
            get_value(row, ["summaries_text"]),
        )

    birth_countries = ensure_country_nodes(g, origin_val)

    # Determine geometry once per row and reuse for all individual events.
    lat, lon = parse_coordinates_from_fields(latitude_val, longitude_val)
    if lat is not None and lon is not None:
        count_geo_from_csv += 1
    else:
        lat, lon = parse_coordinates_from_location(location_val)
        if lat is None or lon is None:
            lat, lon = geocode_location(location_val)
        if lat is not None and lon is not None:
            count_geocoded += 1
        elif not is_missing(location_val):
            count_geocode_skipped += 1

    collective_event_uri = None
    if total_dead_missing >= 2:
        collective_event_uri = DATA[f"allemagne_CollectiveEvent_{row_num}"]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, COLLECTIVE_EVENT_CLASS))
            g.add((collective_event_uri, PROP_totalDeadAndMissing, Literal(total_dead_missing, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_numberDead, Literal(number_dead, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_numberMissing, Literal(number_missing, datatype=XSD.integer)))
            if not is_missing(details_val):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(details_val).strip())))
            created_collective_events.add(str(collective_event_uri))
            count_collective_events += 1

    person_event_pairs = []

    for victim_pos in range(victim_total):
        person_uri = DATA[f"allemagne_Person_{row_num}_{victim_pos + 1}"]
        g.add((person_uri, RDF.type, PERSON_CLASS))
        count_person += 1

        is_missing_victim = victim_pos >= number_dead
        # Garder des familles d'URI deterministes par type d'evenement pour des diffs TTL stables.
        if is_missing_victim:
            event_uri = DATA[f"allemagne_MissingEvent_{row_num}_{victim_pos + 1}"]
            g.add((event_uri, RDF.type, MISSING_EVENT_CLASS))
            count_missing_events += 1
        else:
            event_uri = DATA[f"allemagne_Death_{row_num}_{victim_pos + 1}"]
            g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
            count_death_events += 1

        g.add((event_uri, RDF.type, F.IndividualEvent))
        count_individual_events += 1

        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, PROP_group, collective_event_uri))

        if not is_missing(name_val):
            g.add((person_uri, PROP_hasName, Literal(str(name_val).strip())))

        if normalized_gender == "male":
            g.add((person_uri, PROP_gender, GENDER_URIS["male"]))
        elif normalized_gender == "female":
            g.add((person_uri, PROP_gender, GENDER_URIS["female"]))
        else:
            g.add((person_uri, PROP_gender, GENDER_URIS["unknown"]))

        if birth_literal_value is not None:
            g.add((person_uri, PROP_yearOfBirth, birth_literal_value))
        elif birth_literal_text == "unknown":
            g.add((person_uri, PROP_yearOfBirth, Literal("unknown")))

        for country_uri in birth_countries:
            g.add((person_uri, PROP_birthPlace, country_uri))

        age_node = create_age_node(g, age_values, idx, victim_pos)
        if age_node is not None:
            g.add((person_uri, PROP_hasAgeLink, age_node))

        if death_iso is not None:
            g.add((event_uri, TIME.inXSDDate, Literal(death_iso, datatype=XSD.date)))
            weekday_name = infer_day_of_week_name(death_iso)
            if weekday_name:
                g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
        if date_comment is not None:
            g.add((event_uri, PROP_hasComment, Literal(date_comment)))
        if not is_missing(details_val):
            g.add((event_uri, PROP_hasNarrative, Literal(str(details_val).strip())))

        if not is_missing(cause_val):
            cause_uri, cause_label, cause_nature, is_literal = match_death_cause(cause_val, mapping_dict, thesaurus_map, mapping_nature)

            # La sortie DeathCause est volontairement desactivee pour l'export Allemagne.
            if cause_nature is not None:
                nature_norm = norm(cause_nature)
                nature_match_uri = None
                if nature_norm in ("accident", "homicide", "suicide"):
                    nature_match_uri = T[nature_norm]
                elif nature_norm in ("inconnu", "unknown", "medical", "médical"):
                    nature_match_uri = T.deathNature

                death_nature_instance = create_or_get_death_nature_instance(g, cause_nature, nature_match_uri)
                if death_nature_instance is not None:
                    g.add((event_uri, PROP_hasDeathNature, death_nature_instance))
                    count_nature_mapped += 1

            if cause_uri is not None:
                count_cause_matched += 1
            elif cause_label is not None:
                count_cause_from_raw += 1

        if lat is not None and lon is not None and not is_suspicious_coordinate(lat, lon):
            geometry_uri = DATA[f"allemagne_geometry_{row_num}_{victim_pos + 1}"]
            g.add((event_uri, GEO.hasGeometry, geometry_uri))
            g.add((geometry_uri, RDF.type, GEO.Geometry))
            g.add((geometry_uri, GEO.asWKT, Literal(f"POINT({lon} {lat})", datatype=GEO.wktLiteral)))

        person_event_pairs.append((person_uri, event_uri))

    # Evenements Injury: detection depuis le texte narratif/info
    combined_narrative = " ".join(filter(None, [
        str(details_val).strip() if not is_missing(details_val) else "",
        get_value(row, ["info_text"]) or "",
    ]))
    # Transport deduit du texte de cause.
    transport_token = detect_transport_from_cause(cause_val, combined_narrative)
    injury_kws = ["verletzt", "verwundet", "blessé", "injured", "injury", "wound", "ferito", "herido"]
    if any(kw in combined_narrative.lower() for kw in injury_kws):
        for victim_pos, (person_uri, base_event_uri) in enumerate(person_event_pairs, start=1):
            injury_uri = DATA[f"allemagne_InjuryEvent_{row_num}_{victim_pos}"]
            g.add((injury_uri, RDF.type, INJURY_EVENT_CLASS))
            g.add((injury_uri, RDF.type, F.IndividualEvent))
            g.add((person_uri, PROP_composedOf, injury_uri))
            g.add((injury_uri, PROP_temporal_before, base_event_uri))
            g.add((base_event_uri, PROP_temporal_after, injury_uri))
            if collective_event_uri is not None:
                g.add((injury_uri, PROP_group, collective_event_uri))
            if death_iso is not None:
                g.add((injury_uri, TIME.inXSDDate, Literal(death_iso, datatype=XSD.date)))

    if transport_token is not None:
        transport_uri = DATA[f"allemagne_Transport_{slugify(transport_token)}_{row_num}"]
        if str(transport_uri) not in created_transports:
            g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
            g.add((transport_uri, PROP_transportName, Literal(transport_token)))
            created_transports.add(str(transport_uri))
            count_transports += 1
        for _, event_uri in person_event_pairs:
            g.add((event_uri, PROP_transportType, transport_uri))

    # Creer des evenements typés supplementaires (Inhumation, Control, Trace, etc.) a partir de l'analyse textuelle.
    matched_specs = detect_additional_event_specs(text_chunks_for_typing, ADDITIONAL_EVENT_SPECS)
    if matched_specs:
        type_snippet = " | ".join(text_chunks_for_typing)[:800]
        for victim_pos, (person_uri, base_event_uri) in enumerate(person_event_pairs, start=1):
            for spec in matched_specs:
                slug = slugify(spec["name"])
                extra_uri = DATA[f"allemagne_{slug}Event_{row_num}_{victim_pos}"]
                g.add((extra_uri, RDF.type, spec["class_uri"]))
                g.add((extra_uri, RDF.type, F.IndividualEvent))
                g.add((person_uri, PROP_composedOf, extra_uri))
                if collective_event_uri is not None:
                    g.add((extra_uri, PROP_group, collective_event_uri))

                # Les evenements post-mortem surviennent apres l'evenement de base death/injury/missing.
                if spec["post_mortem"]:
                    g.add((base_event_uri, PROP_temporal_before, extra_uri))
                    g.add((extra_uri, PROP_temporal_after, base_event_uri))
                else:
                    g.add((extra_uri, PROP_temporal_before, base_event_uri))
                    g.add((base_event_uri, PROP_temporal_after, extra_uri))

                g.add((extra_uri, PROP_hasComment, Literal(f"Detected event type: {spec['name']}")))
                g.add((extra_uri, PROP_hasNarrative, Literal(type_snippet)))

                if spec["name"] == "Inhumation":
                    count_inhumation_events += 1
                count_additional_typed_events += 1

    # Noeud source: URL dans hasComment; libelle depuis Information Source,
    # ou URL quand Information Source est vide.
    if not is_missing(source_url_val) or not is_missing(info_source_val):
        source_label = str(info_source_val).strip() if not is_missing(info_source_val) else str(source_url_val).strip()
        source_slug = slugify(source_label)
        source_uri = DATA[f"allemagne_Source_{row_num}_{source_slug}"]
        g.add((source_uri, RDF.type, SOURCE_CLASS))

        source_category = infer_source_category_key(source_label, source_url_val, sources_text_val or "")
        # German newspapers/media not caught by generic patterns
        if source_category is None:
            src_norm = norm(str(sources_text_val or source_label or ""))
            de_media = ["taz", " sz ", "spiegel", " nd ", " fr ", "stuttgarter", "konkret", "pressespiegel",
                        "handelsblatt", "welt", "bild", "stern", "focus", "zeit", " faz ", "tagesspiegel",
                        "morgenpost", "rundschau", "anzeiger", "zeitung", "journal", "imedana", "radio",
                        "tv ", "fernsehen", "nachricht", "reportage", "facebook", "twitter", "instagram",
                        "online", "artikel", "bericht", "presse", "broadcast", "magazine"]
            de_civil = ["pro asyl", "amnesty", "flüchtlingshilfe", "caritas", "diakonie", "rotes kreuz",
                        "awо", "awo", "sos", "ngо", "ngo", "hilfswerk", "verein", "initiative",
                        "human rights", "abad", "humanitär"]
            if any(kw in src_norm for kw in de_media):
                source_category = "media"
            elif any(kw in src_norm for kw in de_civil):
                source_category = "civil_society"
        if source_category == "family":
            g.add((source_uri, RDF.type, F.Family))
        elif source_category == "media":
            g.add((source_uri, RDF.type, F.Media))
        elif source_category == "civil_society":
            g.add((source_uri, RDF.type, F.CivilSociety))
        elif source_category == "death_certificate":
            g.add((source_uri, RDF.type, F.DeathCertificate))
        elif source_category == "official_document":
            g.add((source_uri, RDF.type, F.OtherOfficialDocument))
        else:
            # Repli par defaut pour Allemagne: les sources ARI-dok sont traitees comme media/presse
            g.add((source_uri, RDF.type, F.Media))

        if source_label:
            g.add((source_uri, RDFS.label, Literal(source_label)))
        if not is_missing(source_url_val):
            g.add((source_uri, PROP_hasComment, Literal(str(source_url_val).strip())))

        for _, event_uri in person_event_pairs:
            g.add((event_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

# -------------------- Process unique summaries_text --------------------
count_summary_collective = 0
count_summary_deaths = 0
count_summary_injuries = 0
count_summary_missing = 0

if "summaries_text" in df.columns:
    processed_summaries: set = set()
    for raw_summary in df["summaries_text"].dropna().unique():
        unique_summary = str(raw_summary).strip()
        if not unique_summary or unique_summary in processed_summaries:
            continue
        processed_summaries.add(unique_summary)

        counts = parse_summaries_text_events(unique_summary)
        n_deaths = counts["deaths"]
        n_injuries = counts["injuries"]
        n_missing = counts["missing"]
        year = counts["year"]

        total = n_deaths + n_injuries + n_missing
        if total == 0:
            continue

        summary_slug = str(year) if year else slugify(unique_summary[:50])
        coll_uri = DATA[f"allemagne_SummaryCollectiveEvent_{summary_slug}"]
        g.add((coll_uri, RDF.type, COLLECTIVE_EVENT_CLASS))
        g.add((coll_uri, PROP_numberDead, Literal(n_deaths, datatype=XSD.integer)))
        g.add((coll_uri, PROP_numberMissing, Literal(n_missing, datatype=XSD.integer)))
        g.add((coll_uri, PROP_totalDeadAndMissing, Literal(n_deaths + n_missing, datatype=XSD.integer)))
        g.add((coll_uri, PROP_hasNarrative, Literal(unique_summary)))
        if year:
            g.add((coll_uri, TIME.inXSDDate, Literal(str(year), datatype=XSD.gYear)))
        count_summary_collective += 1

        for i in range(n_deaths):
            ev = DATA[f"allemagne_SummaryDeath_{summary_slug}_{i + 1}"]
            pers = DATA[f"allemagne_SummaryPerson_{summary_slug}_d{i + 1}"]
            g.add((ev, RDF.type, DEATH_EVENT_CLASS))
            g.add((ev, RDF.type, F.IndividualEvent))
            g.add((pers, RDF.type, PERSON_CLASS))
            g.add((pers, PROP_composedOf, ev))
            g.add((ev, PROP_group, coll_uri))
            if year:
                g.add((ev, TIME.inXSDDate, Literal(str(year), datatype=XSD.gYear)))
            count_summary_deaths += 1

        for i in range(n_injuries):
            ev = DATA[f"allemagne_SummaryInjuryEvent_{summary_slug}_{i + 1}"]
            pers = DATA[f"allemagne_SummaryPerson_{summary_slug}_inj{i + 1}"]
            g.add((ev, RDF.type, INJURY_EVENT_CLASS))
            g.add((ev, RDF.type, F.IndividualEvent))
            g.add((pers, RDF.type, PERSON_CLASS))
            g.add((pers, PROP_composedOf, ev))
            g.add((ev, PROP_group, coll_uri))
            if year:
                g.add((ev, TIME.inXSDDate, Literal(str(year), datatype=XSD.gYear)))
            count_summary_injuries += 1

        for i in range(n_missing):
            ev = DATA[f"allemagne_SummaryMissingEvent_{summary_slug}_{i + 1}"]
            pers = DATA[f"allemagne_SummaryPerson_{summary_slug}_mis{i + 1}"]
            g.add((ev, RDF.type, MISSING_EVENT_CLASS))
            g.add((ev, RDF.type, F.IndividualEvent))
            g.add((pers, RDF.type, PERSON_CLASS))
            g.add((pers, PROP_composedOf, ev))
            g.add((ev, PROP_group, coll_uri))
            if year:
                g.add((ev, TIME.inXSDDate, Literal(str(year), datatype=XSD.gYear)))
            count_summary_missing += 1

# ------------------------ Sortie ------------------------
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "=" * 62)
print("Import Allemagne complete")
print("=" * 62)
print(f"Rows processed                 : {len(df)}")
print(f"Persons created               : {count_person}")
print(f"Individual events created     : {count_individual_events}")
print(f"Death events created          : {count_death_events}")
print(f"Missing events created        : {count_missing_events}")
print(f"Collective events created     : {count_collective_events}")
print(f"Inhumation events created     : {count_inhumation_events}")
print(f"Other typed events created    : {count_additional_typed_events}")
print(f"Transport individuals created : {count_transports}")
print(f"Sources created               : {count_sources}")
print(f"Cause instances from mapping  : {count_cause_matched}")
print(f"Cause instances from raw text : {count_cause_from_raw}")
print(f"Death nature mapped           : {count_nature_mapped}")
print(f"Geometry from latitude/longitude: {count_geo_from_csv}")
print(f"Geometry from geocoding       : {count_geocoded}")
print(f"Geocoding unresolved/skipped  : {count_geocode_skipped}")
print(f"Date fallback from morgue out : {count_date_from_morgue_taken}")
print(f"Date fallback from morgue in  : {count_date_from_brought_to_morgue}")
print("=" * 62)
print(f"Output written to: {OUTPUT_TTL}")
if count_summary_collective:
    print(f"\nSummaries_text events:")
    print(f"  Summary collective events : {count_summary_collective}")
    print(f"  Summary death events      : {count_summary_deaths}")
    print(f"  Summary injury events     : {count_summary_injuries}")
    print(f"  Summary missing events    : {count_summary_missing}")


