#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV Migrant Files -> ontologie RDF selon les regles Frontlet.
"""

from rdflib import Graph, Namespace, URIRef, BNode, Literal
from rdflib.namespace import RDF, RDFS, SKOS, XSD
import pandas as pd
import unicodedata
import re
import os
import math
import pycountry
from datetime import datetime
from geopy.geocoders import Nominatim
from geopy.exc import GeocoderTimedOut, GeocoderServiceError
import time
from event_text_utils import (
    add_additional_typed_events,
    build_additional_event_specs,
    collect_text_values_from_row,
    infer_day_of_week_name,
    infer_source_category_key,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
CSV_PATH = "Migrant_files/Migrant Files - Events that were not in Uniteds list.csv"
OUTPUT_TTL = "Migrant_files/frontlet_import_output.ttl"
MAPPING_PATH = "Migrant_files/mappingMigrantFilesThesaurusCauseMort.csv"  # Optionnel

# Espaces de noms par defaut
F = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")

# ----------------- Fonctions utilitaires ----------------
def norm(s):
    """Normalize string for comparisons."""
    if s is None:
        return ""
    s = str(s).strip()
    s = unicodedata.normalize("NFKD", s)
    s = re.sub(r"\s+", " ", s)
    return s.lower()


def is_missing(s):
    """Return True for None/empty or common null tokens."""
    if s is None:
        return True
    s_norm = norm(s)
    if s_norm == "":
        return True
    if s_norm in ("nan", "none", "n/a", "na", "-"):
        return True
    return False


def parse_int_value(value):
    """Parse an integer from values like '8', '8.0', '8 people'."""
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

def parse_coordinate_value(value):
    """Extract a coordinate float from strings like 'LAT 39.214156'."""
    if is_missing(value):
        return None
    text = str(value).strip().replace(",", ".")
    match = re.search(r"[-+]?\d*\.?\d+", text)
    if not match:
        return None
    try:
        return float(match.group(0))
    except Exception:
        return None


def parse_date_or_year(date_value, year_value):
    """
    Parse Date to YYYY-MM-DD, ignoring time components (e.g., ISO with 'T...Z').
    If Date is missing, return a fallback year string.
    Returns tuple: (iso_date_or_none, year_or_none)
    """
    if not is_missing(date_value):
        date_text = str(date_value).strip()
        candidates = [
            "%Y-%m-%dT%H:%M:%SZ",
            "%Y-%m-%d",
            "%d/%m/%Y %H:%M",
            "%d/%m/%Y",
        ]
        for fmt in candidates:
            try:
                d = datetime.strptime(date_text, fmt)
                return d.strftime("%Y-%m-%d"), None
            except ValueError:
                continue

        # Derniere tentative: conserver seulement la partie date avant le separateur T ou espace.
        raw_date = re.split(r"[T\s]", date_text)[0]
        for fmt in ("%Y-%m-%d", "%d/%m/%Y"):
            try:
                d = datetime.strptime(raw_date, fmt)
                return d.strftime("%Y-%m-%d"), None
            except ValueError:
                continue

    if not is_missing(year_value):
        year_match = re.search(r"\b(\d{4})\b", str(year_value))
        if year_match:
            return None, year_match.group(1)

    return None, None


def parse_age_from_text(*values):
    """Extract a precise age from free text (e.g. 12 years old, aged 30)."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return None

    patterns = [
        r"\b(\d{1,3})\s*(?:years?\s*old|year-old|yrs?\s*old|yo)\b",
        r"\baged\s*(\d{1,3})\b",
    ]
    for pattern in patterns:
        m = re.search(pattern, txt)
        if not m:
            continue
        try:
            age = int(m.group(1))
            if 0 < age <= 120:
                return age
        except Exception:
            continue
    return None


def parse_age_interval_from_text(*values):
    """Extract an age interval from text (e.g. between 18 and 25 years old)."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return None

    patterns = [
        r"\bbetween\s*(\d{1,3})\s*(?:and|-)\s*(\d{1,3})\s*(?:years?|yrs?)?\b",
        r"\bfrom\s*(\d{1,3})\s*(?:to|-)\s*(\d{1,3})\s*(?:years?|yrs?)?\b",
        r"\b(\d{1,3})\s*[-–]\s*(\d{1,3})\s*(?:years?|yrs?)\b",
    ]
    for pattern in patterns:
        m = re.search(pattern, txt)
        if not m:
            continue
        try:
            a = int(m.group(1))
            b = int(m.group(2))
            if 0 < a <= 120 and 0 < b <= 120:
                return (min(a, b), max(a, b))
        except Exception:
            continue
    return None


def estimate_dead_missing_injury_counts(row):
    """Estimate dead/missing/injury counts using explicit columns and text evidence."""
    desc = str(row.get("Description", "") or "")
    txt = norm(desc)
    total_dead_missing = parse_int_value(row.get("Dead and missing", "")) or 0

    def _extract(pattern):
        m = re.search(pattern, txt)
        if not m:
            return 0
        try:
            return max(0, int(m.group(1)))
        except Exception:
            return 0

    dead = _extract(r"\b(\d{1,4})\s+(?:dead|killed|drowned|deaths?)\b")
    missing = _extract(r"\b(\d{1,4})\s+(?:missing|disappeared)\b")
    injury = _extract(r"\b(\d{1,4})\s+(?:injured|wounded|hurt)\b")

    if dead == 0 and any(k in txt for k in [" dead", "killed", "drowned", "body recovered", "bodies recovered"]):
        dead = 1
    if missing == 0 and any(k in txt for k in [" missing", "disappeared"]):
        missing = 1
    if injury == 0 and any(k in txt for k in ["injured", "wounded", "hurt"]):
        injury = 1

    if total_dead_missing > 0:
        if dead + missing == 0:
            dead = total_dead_missing
        elif dead + missing < total_dead_missing:
            missing += (total_dead_missing - (dead + missing))

    if dead <= 0 and missing <= 0:
        dead = 1

    return dead, missing, injury


def detect_transport_from_text(*values):
    """Detect transport token from text."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return None

    patterns = [
        ("boat", ["boat", "ship", "vessel", "canoe", "raft", "patera", "dinghy", "kwassa"]),
        ("truck", ["truck", "lorry", "trailer", "container"]),
        ("train", ["train", "rail", "railway"]),
        ("bus", ["bus", "coach", "minibus"]),
        ("car", ["car", "vehicle", "van", "automobile"]),
        ("plane", ["plane", "flight", "aircraft", "undercarriage"]),
        ("on_foot", ["on foot", "walk", "walking", "desert", "minefield"]),
    ]
    for token, keywords in patterns:
        if any(k in txt for k in keywords):
            return token
    return None


def find_by_label(g, search, props=(RDFS.label, SKOS.prefLabel)):
    """Return first subject in graph whose label/prefLabel matches search."""
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


# Initialiser le geocodeur
geolocator = Nominatim(user_agent="frontlet_migrant_files_geocoder")
GEOCODING_MAX_CALLS = 10
geocoding_calls_count = 0


def geocode_location(location_name, max_retries=3):
    """Geocode un lieu et retourne (latitude, longitude) ou (None, None)."""
    global geocoding_calls_count

    if is_missing(location_name):
        return None, None

    if geocoding_calls_count >= GEOCODING_MAX_CALLS:
        return None, None

    location_str = str(location_name).strip()

    for attempt in range(max_retries):
        try:
            geocoding_calls_count += 1
            location = geolocator.geocode(location_str, timeout=10)
            if location:
                return location.latitude, location.longitude
            return None, None
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                time.sleep(1)
                continue
            print(f"Geocoding timeout for: {location_name}")
            return None, None
        except GeocoderServiceError as e:
            print(f"Geocoding service error for {location_name}: {e}")
            return None, None
        except Exception as e:
            print(f"Unexpected geocoding error for {location_name}: {e}")
            return None, None

    return None, None


def is_suspicious_coordinate(lat, lon):
    """Check if coordinates are suspicious and should be ignored."""
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return True, "PARSE_ERROR"

    if lon == -99 and lat == -99:
        return True, "ERROR_-99,-99"
    if -14 < lat < -12 and 43 < lon < 45:
        return True, "Madagascar_NW"
    if lat > 70:
        return True, "High_North"
    if abs(lon) > 180 or abs(lat) > 90:
        return True, "OUT_OF_BOUNDS"

    return False, "OK"


def ensure_country_node(g, country_code_or_name):
    """Find or create a country resource from name/code."""
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    cc = None
    sval = re.sub(r"[^A-Za-z0-9]", "", val).upper()
    try:
        if re.fullmatch(r"[A-Z]{2}", sval):
            c = pycountry.countries.get(alpha_2=sval)
            if c:
                cc = c
        elif re.fullmatch(r"[A-Z]{3}", sval):
            c = pycountry.countries.get(alpha_3=sval)
            if c:
                cc = c
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
        iso3 = getattr(cc, "alpha_3", None) or getattr(cc, "alpha_2", None)
        if not iso3:
            return None
        uri = DATA["migrant_Country_" + iso3.upper()]
        if (uri, None, None) not in g:
            g.add((uri, RDF.type, F.Country))
            en_label = Literal(getattr(cc, "name", val), lang="en")
            if (uri, RDFS.label, en_label) not in g:
                g.add((uri, RDFS.label, en_label))
            g.add((uri, F.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            g.add((uri, F.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            g.add((uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return uri

    candidate = find_by_label(g, country_code_or_name)
    if candidate:
        return candidate

    slug = re.sub(r"[^a-z0-9_]", "_", norm(country_code_or_name))
    if slug in ("", "nan", "none", "n_a"):
        return None
    uri = DATA["migrant_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(country_code_or_name)))
    return uri


def find_thesaurus_term_by_prefLabel_fr(g, label_fr):
    """Search thesaurus for a subject with SKOS:prefLabel == label_fr."""
    if label_fr is None or str(label_fr).strip() == "":
        return None
    for s, _, o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == norm(label_fr):
            return s
    for s, _, o in g.triples((None, RDFS.label, None)):
        if norm(o) == norm(label_fr):
            return s
    return None


# ---------------- Utilitaires du thesaurus ----------------
def load_death_cause_thesaurus(g):
    """Load DeathCause thesaurus: normalized label -> URI."""
    cause_map = {}
    try:
        for cause_uri in g.subjects(RDF.type, T.DeathCause):
            for label_obj in g.objects(cause_uri, SKOS.prefLabel):
                if label_obj.language == "fr" or label_obj.language is None:
                    label_norm = norm(str(label_obj))
                    if label_norm:
                        cause_map[label_norm] = cause_uri
        print(f"Loaded {len(cause_map)} DeathCause entries from thesaurus")
    except Exception as e:
        print(f"Warning: Could not load DeathCause thesaurus: {e}")
    return cause_map


def load_mapping_csv(mapping_path=MAPPING_PATH):
    """Load optional CSV mapping: col1=raw value, col2=thesaurus prefLabel, col3=Nature (optional)."""
    mapping = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, direct matching only")
        return mapping, mapping_nature
    try:
        mdf = pd.read_csv(mapping_path, sep=";", dtype=str)
        cols = list(mdf.columns)
        if len(cols) >= 2:
            raw_col = cols[0]
            thes_col = cols[1]
            nature_col = cols[2] if len(cols) >= 3 and "nature" in str(cols[2]).lower() else None
            for _, r in mdf.iterrows():
                a = norm(r.get(raw_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
                if nature_col:
                    n = str(r.get(nature_col, "")).strip()
                    if a and n and n.lower() not in ("", "nan", "none"):
                        mapping_nature[a] = n
            print(f"Loaded {len(mapping)} custom mappings from CSV")
        else:
            print(f"Warning: Expected at least 2 columns in {mapping_path}")
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping, mapping_nature


def match_death_cause(value, mapping_dict, thesaurus_map):
    """Match cause to thesaurus URI or fallback literal."""
    if not value or is_missing(value):
        return None, None, False

    val_norm = norm(value)

    mapped_label = mapping_dict.get(val_norm)
    if mapped_label:
        uri = thesaurus_map.get(mapped_label)
        if uri:
            return uri, mapped_label, False
        return None, mapped_label, True

    if val_norm in thesaurus_map:
        return thesaurus_map[val_norm], val_norm, False

    for lbl, uri in thesaurus_map.items():
        if lbl and lbl in val_norm:
            return uri, lbl, False

    val_words = set(re.findall(r"\b\w+\b", val_norm))
    best = (None, None, 0)
    for lbl, uri in thesaurus_map.items():
        lbl_words = set(re.findall(r"\b\w+\b", lbl))
        overlap = len(val_words & lbl_words)
        if overlap > best[2] and overlap >= 2:
            best = (uri, lbl, overlap)
    if best[0]:
        return best[0], best[1], False

    return None, str(value).strip(), True


def create_age_node(graph, age_value, row_num):
    """Create a frontlet:Age instance."""
    if age_value is None:
        return None
    try:
        age_num = int(age_value)
    except Exception:
        return None
    age_uri = DATA[f"migrant_Age_{row_num}"]
    graph.add((age_uri, RDF.type, F.Age))
    graph.add((age_uri, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    return age_uri


def create_age_interval_node(graph, age_interval, row_num):
    """Create a frontlet:AgeInterval instance."""
    if not age_interval:
        return None
    age_min, age_max = age_interval
    age_interval_uri = DATA[f"migrant_AgeInterval_{row_num}"]
    graph.add((age_interval_uri, RDF.type, F.AgeInterval))
    graph.add((age_interval_uri, RDFS.label, Literal(f"{age_min}-{age_max} years")))
    return age_interval_uri


def create_or_get_death_cause_instance(graph, label_text, row_num, match_uri=None):
    """Create/reuse a frontlet:DeathCause individual."""
    if is_missing(label_text):
        return None
    slug = re.sub(r"[^a-z0-9_]", "_", norm(label_text)).strip("_")
    if slug == "":
        return None
    uri = DATA[f"migrant_DeathCause_{slug}"]
    if (uri, RDF.type, F.DeathCause) not in graph:
        graph.add((uri, RDF.type, F.DeathCause))
        graph.add((uri, RDFS.label, Literal(str(label_text).strip())))
        if match_uri is not None:
            graph.add((uri, SKOS.closeMatch, match_uri))
    return uri


def infer_nature_from_cause_text(cause_text, mapped_nature=None):
    """Infer death nature from mapping or cause text."""
    if not is_missing(mapped_nature):
        return str(mapped_nature).strip()

    txt = norm(cause_text)
    if any(k in txt for k in ["suicide", "self-harm", "self harm"]):
        return "suicide"
    if any(k in txt for k in ["murder", "shot", "stab", "violence", "beaten", "assault"]):
        return "homicide"
    if any(k in txt for k in ["ill-treatment", "ill treatment", "medical", "sickness", "disease"]):
        return "medical"
    if any(k in txt for k in ["unknown", "mixed"]):
        return "unknown"
    return "accident"


def create_or_get_death_nature_instance(graph, label_text):
    """Create/reuse a frontlet:DeathNature individual."""
    if is_missing(label_text):
        return None
    slug = re.sub(r"[^a-z0-9_]", "_", norm(label_text)).strip("_")
    if slug == "":
        return None
    uri = DATA[f"migrant_DeathNature_{slug}"]
    if (uri, RDF.type, F.DeathNature) not in graph:
        graph.add((uri, RDF.type, F.DeathNature))
        graph.add((uri, RDFS.label, Literal(str(label_text).strip())))
    return uri


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
encodings_to_try = ["utf-8-sig", "utf-8", "cp1252", "latin-1"]
df = None
for _enc in encodings_to_try:
    try:
        df = pd.read_csv(
            CSV_PATH,
            sep=",",
            engine="python",
            dtype=str,
            keep_default_na=False,
            na_values=["", "NaN", "nan"],
            encoding=_enc,
        )
        break
    except UnicodeDecodeError:
        continue
if df is None:
    raise RuntimeError(f"Unable to read CSV file: {CSV_PATH}")

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or F.Injury
MISSING_EVENT_CLASS = F.Missing
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_CERTIFICATE_CLASS = find_by_label(g_ref, "DeathCertificate") or F.DeathCertificate

PROP_composedOf = find_by_label(g_ref, "composedOf") or F.composedOf
PROP_borderOUT = find_by_label(g_ref, "borderOUT") or F.borderOUT
PROP_borderIN = find_by_label(g_ref, "borderIN") or F.borderIN
PROP_hasAgeLink = find_by_label(g_ref, "aged") or F.aged
PROP_hasAgeInterval = find_by_label(g_ref, "has age interval") or F.hasAgeInterval
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasWebLink = find_by_label(g_ref, "hasWebLink") or F.hasWebLink
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_certificate = find_by_label(g_ref, "certificate") or F.certificate
PROP_hasIdCertificate = find_by_label(g_ref, "hasIdCertificate") or F.hasIdCertificate
PROP_hasNarrative = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_totalDeadAndMissing = find_by_label(g_ref, "total dead and missing") or F.totalDeadAndMissing
PROP_dateDeMort = find_by_label(g_ref, "Date de mort") or F.dateDeMort
PROP_transportName = find_by_label(g_ref, "transport name") or F.transportName
PROP_transportType = find_by_label(g_ref, "transport type") or F.transportType
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label)
THES_human = T.human

# ------------------- Traitement des lignes ----------------
created_death_events = {}
created_missing_events = {}
created_injury_events = {}
created_collective_events = {}
created_transports = {}

count_person = 0
count_death_events = 0
count_missing_events = 0
count_injury_events = 0
count_collective_events = 0
count_transports = 0
count_cause_matched = 0
count_cause_literal = 0
count_sources = 0
count_death_certificates = 0
count_geocoded_from_location = 0
count_additional_typed_events = 0

for idx, row in df.iterrows():
    row_num = idx + 1

    person_uri = DATA[f"migrant_Person_{row_num}"]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1

    # Repartition des victimes: dead / missing / injury depuis les colonnes + l'analyse de texte.
    dead_count, missing_count, injury_count = estimate_dead_missing_injury_counts(row)
    if injury_count > 0 and (dead_count + missing_count) == 0:
        # Injury ne peut pas etre seul: imposer au moins un ancrage death/disappearance.
        missing_count = 1
    total_dead_missing = dead_count + missing_count

    collective_event_uri = None
    if total_dead_missing >= 2:
        collective_event_uri = DATA[f"migrant_CollectiveEvent_{row_num}"]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            g.add((collective_event_uri, RDFS.label, Literal(f"Collective event {row_num}")))
            g.add((collective_event_uri, PROP_totalDeadAndMissing, Literal(total_dead_missing, datatype=XSD.integer)))

            desc = row.get("Description", "")
            if not is_missing(desc):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(desc).strip())))

            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Description", "Cause of death", "Location", "death-in"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Source", "Source URL", "crossing-from", "crossing-to"], is_missing))

    event_uris = []
    death_event_uris = []
    for death_idx in range(max(0, dead_count)):
        # Les IDs d'evenements de deces restent stables par ligne et par rang de victime.
        event_uri = DATA[f"migrant_Death_{row_num}_{death_idx + 1}"]
        if str(event_uri) not in created_death_events:
            g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_death_events[str(event_uri)] = event_uri
            count_death_events += 1
        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))
        event_uris.append(event_uri)
        death_event_uris.append(event_uri)

    for miss_idx in range(max(0, missing_count)):
        event_uri = DATA[f"migrant_MissingEvent_{row_num}_{miss_idx + 1}"]
        if str(event_uri) not in created_missing_events:
            g.add((event_uri, RDF.type, MISSING_EVENT_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_missing_events[str(event_uri)] = event_uri
            count_missing_events += 1
        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))
        event_uris.append(event_uri)

    injury_anchor_event_uri = death_event_uris[0] if death_event_uris else (event_uris[0] if event_uris else None)

    for inj_idx in range(max(0, injury_count)):
        event_uri = DATA[f"migrant_InjuryEvent_{row_num}_{inj_idx + 1}"]
        if str(event_uri) not in created_injury_events:
            g.add((event_uri, RDF.type, INJURY_EVENT_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_injury_events[str(event_uri)] = event_uri
            count_injury_events += 1
        g.add((person_uri, PROP_composedOf, event_uri))
        if injury_anchor_event_uri is not None:
            g.add((event_uri, PROP_temporal_before, injury_anchor_event_uri))
            g.add((injury_anchor_event_uri, PROP_temporal_after, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))
        event_uris.append(event_uri)

    if not event_uris:
        event_uri = DATA[f"migrant_Death_{row_num}_1"]
        g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, event_uri))
        event_uris.append(event_uri)
        death_event_uris.append(event_uri)
        count_death_events += 1

    age_value = parse_age_from_text(row.get("Description", ""), row.get("Cause of death", ""))
    if age_value is not None:
        age_uri = create_age_node(g, age_value, row_num)
        if age_uri is not None:
            g.add((person_uri, PROP_hasAgeLink, age_uri))
    else:
        age_interval = parse_age_interval_from_text(row.get("Description", ""), row.get("Cause of death", ""))
        if age_interval is not None:
            age_interval_uri = create_age_interval_node(g, age_interval, row_num)
            if age_interval_uri is not None:
                g.add((person_uri, PROP_hasAgeInterval, age_interval_uri))

    # DATE depuis "Date"; repli sur "Year"
    iso_date, fallback_year = parse_date_or_year(row.get("Date", ""), row.get("Year", ""))
    if iso_date:
        weekday_name = infer_day_of_week_name(iso_date)
        for ev_uri in event_uris:
            g.add((ev_uri, TIME.inXSDDate, Literal(iso_date, datatype=XSD.date)))
            if weekday_name:
                g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name]))
                g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
    elif fallback_year:
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_dateDeMort, Literal(fallback_year)))

    # Pays: on garde uniquement le pays d'origine / naissance, pas le pays de mort.
    origin_country = row.get("crossing-from", "")
    if not is_missing(origin_country):
        origin_node = ensure_country_node(g, str(origin_country).strip())
        if origin_node is not None:
            g.add((person_uri, F.birthPlace, origin_node))

    # FRONTIER OUT from "crossing-from"
    cross_from = row.get("crossing-from", "")
    if not is_missing(cross_from):
        cnode = ensure_country_node(g, str(cross_from).strip())
        if cnode:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_borderOUT, cnode))

    # FRONTIER IN from "crossing-to"
    cross_to = row.get("crossing-to", "")
    if not is_missing(cross_to):
        cnode = ensure_country_node(g, str(cross_to).strip())
        if cnode:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_borderIN, cnode))

    # TRANSPORT deduit des textes route/cause/description
    route_val = row.get("route", "") or row.get("Route", "") or row.get("Migration route", "")
    transport_token = detect_transport_from_text(route_val, row.get("Cause of death", ""), row.get("Description", ""))
    if transport_token is not None:
        transport_uri = DATA[f"migrant_Transport_{transport_token}_{row_num}"]
        if str(transport_uri) not in created_transports:
            g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
            g.add((transport_uri, PROP_transportName, Literal(transport_token)))
            created_transports[str(transport_uri)] = transport_uri
            count_transports += 1
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_transportType, transport_uri))

        if transport_token == "on_foot":
            for ev_uri in event_uris:
                g.add((ev_uri, F.transportMode, THES_human))
        elif transport_token == "boat":
            for ev_uri in event_uris:
                g.add((ev_uri, F.transportMode, T.boat))

    # CAUSE depuis "Cause of death"
    cause_deces_val = row.get("Cause of death", "")
    if cause_deces_val and not is_missing(cause_deces_val):
        uri, lbl, _is_literal = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        cause_label = lbl if lbl else cause_deces_val
        cause_instance = create_or_get_death_cause_instance(g, cause_label, row_num, uri)
        if cause_instance is not None:
            for ev_uri in death_event_uris:
                g.add((ev_uri, PROP_hasDeathCause, cause_instance))
            count_cause_matched += 1
        elif lbl:
            for ev_uri in death_event_uris:
                g.add((ev_uri, PROP_hasDeathCause, Literal(lbl)))
            count_cause_literal += 1

        nature_label = infer_nature_from_cause_text(cause_deces_val, mapping_nature.get(norm(cause_deces_val)))
        nature_instance = create_or_get_death_nature_instance(g, nature_label)
        if nature_instance is not None:
            for ev_uri in death_event_uris:
                g.add((ev_uri, PROP_hasDeathNature, nature_instance))

    # GEO depuis lng/lat; repli de geocodage depuis Location si l'un manque
    lat_f = parse_coordinate_value(row.get("lat", ""))
    lon_f = parse_coordinate_value(row.get("lng", ""))

    if lat_f is None or lon_f is None:
        location = row.get("Location", "")
        if not is_missing(location):
            lat_geo, lon_geo = geocode_location(location)
            if lat_geo is not None and lon_geo is not None:
                lat_f, lon_f = lat_geo, lon_geo
                count_geocoded_from_location += 1

    if lat_f is not None and lon_f is not None and math.isfinite(lat_f) and math.isfinite(lon_f):
        is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
        if not is_suspicious:
            wkt = f"POINT({lon_f} {lat_f})"
            for ev_pos, ev_uri in enumerate(event_uris, start=1):
                geometry_uri = DATA[f"migrant_geometry_{row_num}_{ev_pos}"]
                g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                g.add((geometry_uri, RDF.type, GEO.Geometry))
                g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
        else:
            print(f"  Warning: suspicious coordinate ignored ({reason}): {lon_f}, {lat_f}")

    # Classe SOURCE derivee de "Source"; URL source mappee vers hasWebLink
    source_name = row.get("Source", "")
    source_url = row.get("Source URL", "")
    has_source_name = not is_missing(source_name)
    has_source_url = not is_missing(source_url)

    if has_source_name or has_source_url:
        source_uri = DATA[f"migrant_Source_{row_num}"]
        g.add((source_uri, RDF.type, F.Source))

        source_name_text = str(source_name).strip() if has_source_name else ""
        source_url_text = str(source_url).strip() if has_source_url else ""
        source_category = infer_source_category_key(source_name_text, source_url_text)
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

        if has_source_url:
            g.add((source_uri, PROP_hasWebLink, Literal(source_url_text)))

        if has_source_name:
            g.add((source_uri, PROP_hasComment, Literal(source_name_text)))
            g.add((source_uri, RDFS.label, Literal(source_name_text)))

        for ev_uri in event_uris:
            g.add((ev_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, ev_uri) for ev_uri in event_uris],
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "migrant",
        row_num,
        F,
        RDF,
        Literal,
        PROP_composedOf,
        F.group,
        PROP_temporal_before,
        PROP_temporal_after,
        PROP_hasComment,
        PROP_hasComment,
    )
    count_additional_typed_events += sum(additional_counts.values())

# --------------------- Resume et sortie ------------------
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "=" * 60)
print("Import Migrant Files complete.")
print("=" * 60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created (IndividualEvent): {count_death_events}")
print(f"Missing events created (IndividualEvent): {count_missing_events}")
print(f"Injury events created (IndividualEvent): {count_injury_events}")
print(f"Collective events created: {count_collective_events}")
print(f"Transport individuals created: {count_transports}")
print(f"Sources created: {count_sources}")
print(f"Death certificates created: {count_death_certificates}")
print(f"Cause matched to thesaurus URI: {count_cause_matched}")
print(f"Cause fallback literal: {count_cause_literal}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Geocoded from Location (missing lng/lat): {count_geocoded_from_location}")
print("=" * 60)
print(f"Output written to: {OUTPUT_TTL}")


