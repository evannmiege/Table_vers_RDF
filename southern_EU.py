#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV UE Sud (southern_eu) -> ontologie RDF selon vos règles.
CSV  : southern_eu/ue_sudMorts.csv
Output : southern_eu/frontlet_import_output.ttl
"""

from rdflib import Graph, Namespace, URIRef, Literal
from rdflib.namespace import RDF, RDFS, SKOS, XSD, OWL
import pandas as pd
import unicodedata
import re
import os
import math
import json
import pycountry
from geopy.geocoders import Nominatim
from geopy.exc import GeocoderTimedOut, GeocoderServiceError
import time
from event_text_utils import (
    add_additional_typed_events,
    build_additional_event_specs,
    collect_text_values_from_row,
    infer_day_of_week_name,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH   = "frontletOnto.ttl"
THES_PATH   = "frontletThesaurus.ttl"
CSV_PATH    = "southern_eu/ue_sudMorts.csv"
OUTPUT_TTL  = "southern_eu/frontlet_import_output.ttl"
MAPPING_PATH = "southern_eu/mappingUE_SudThesaurusCauseMort.csv"
GEOCODE_CACHE_PATH      = "southern_eu/geocode_cache.json"
GEOCODE_MIN_DELAY_SECONDS   = 1.2
GEOCODE_429_BACKOFF_SECONDS = 8.0
GEOCODE_MAX_429_RETRIES     = 2

# Compat mode: mettre ROW_LIMIT a None pour traiter tout le CSV.
ROW_LIMIT = None
ENABLE_GEOCODING = False
STRICT_LITERAL_CAUSE = False

# Espaces de noms par defaut
F    = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T    = Namespace("http://data/frontlet/thesaurus#")
GEO  = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")

# ----------------- Fonctions utilitaires ----------------
def norm(s):
    if s is None:
        return ""
    s = str(s).strip()
    s = unicodedata.normalize("NFKD", s)
    s = re.sub(r"\s+", " ", s)
    return s.lower()


def is_missing(s):
    if s is None:
        return True
    s_norm = norm(s)
    if s_norm == "":
        return True
    if s_norm in ("nan", "none", "n/a", "na", "-", "unknown", "inconnu"):
        return True
    return False


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


def slug(text):
    """Normalise en slug ASCII sans diacritiques."""
    t = unicodedata.normalize("NFD", str(text))
    t = "".join(c for c in t if unicodedata.category(c) != "Mn")
    return re.sub(r"[^A-Za-z0-9_]", "_", t).strip("_")


# --------------------- Géocodage ----------------------
geolocator = Nominatim(user_agent="frontlet_southern_eu_geocoder")
GEOCODER_RATE_LIMITED      = False
LAST_GEOCODE_REQUEST_TS    = 0.0


def load_geocode_cache(path):
    if not os.path.exists(path):
        return {}
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, dict):
            return data
    except Exception:
        pass
    return {}


def save_geocode_cache(path, cache):
    try:
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(cache, fh, ensure_ascii=False, indent=2)
    except Exception:
        pass


def throttle_geocode_requests():
    global LAST_GEOCODE_REQUEST_TS
    now = time.time()
    elapsed = now - LAST_GEOCODE_REQUEST_TS
    if elapsed < GEOCODE_MIN_DELAY_SECONDS:
        time.sleep(GEOCODE_MIN_DELAY_SECONDS - elapsed)
    LAST_GEOCODE_REQUEST_TS = time.time()


def is_http_429_error(err):
    txt = str(err).lower()
    return "429" in txt or "too many requests" in txt


def geocode_location(location_str, geocode_cache, max_retries=3):
    """Géocode une chaîne ville+pays et retourne (lat, lon) ou (None, None)."""
    global GEOCODER_RATE_LIMITED

    if is_missing(location_str):
        return None, None
    if GEOCODER_RATE_LIMITED:
        return None, None

    location_str = str(location_str).strip()
    cache_key = norm(location_str)

    cached = geocode_cache.get(cache_key)
    if isinstance(cached, dict) and "lat" in cached and "lon" in cached:
        try:
            return float(cached["lat"]), float(cached["lon"])
        except Exception:
            pass

    for attempt in range(max_retries):
        try:
            throttle_geocode_requests()
            location = geolocator.geocode(location_str, timeout=10)
            if location:
                lat = float(location.latitude)
                lon = float(location.longitude)
                geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": location_str}
                return lat, lon
            geocode_cache[cache_key] = "NOT_FOUND"
            return None, None
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                time.sleep(1)
                continue
            break
        except GeocoderServiceError as e:
            if is_http_429_error(e):
                for retry in range(GEOCODE_MAX_429_RETRIES):
                    time.sleep(GEOCODE_429_BACKOFF_SECONDS * (retry + 1))
                    try:
                        throttle_geocode_requests()
                        location = geolocator.geocode(location_str, timeout=10)
                        if location:
                            lat = float(location.latitude)
                            lon = float(location.longitude)
                            geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": location_str}
                            return lat, lon
                    except Exception:
                        pass
                GEOCODER_RATE_LIMITED = True
                geocode_cache[cache_key] = "NOT_FOUND"
                return None, None
            break
        except Exception as e:
            if is_http_429_error(e):
                GEOCODER_RATE_LIMITED = True
                geocode_cache[cache_key] = "NOT_FOUND"
                return None, None
            break

    geocode_cache[cache_key] = "NOT_FOUND"
    return None, None


# --------------------- Pays ---------------------------
def ensure_country_node(g, country_code_or_name, prefix="ue_sud"):
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    val = re.sub(r"[*\s]+$", "", val).strip()

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
        uri = DATA[f"{prefix}_Country_{iso3.upper()}"]
        if (uri, None, None) not in g:
            g.add((uri, RDF.type, F.Country))
            g.add((uri, RDF.type, F.Countrydeath))
            g.add((uri, RDFS.label, Literal(getattr(cc, "name", val), lang="en")))
            g.add((uri, F.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            g.add((uri, F.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            g.add((uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return uri

    # Repli: URI basee sur le slug
    s = re.sub(r"[^a-z0-9_]", "_", norm(val))
    if s in ("", "nan", "none", "n_a"):
        return None
    uri = DATA[f"{prefix}_Country_{s}"]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDF.type, F.Countrydeath))
        g.add((uri, RDFS.label, Literal(val)))
    return uri


# --------------------- Âge ----------------------------
def create_age_node(g, age_value, node_suffix):
    """Ressource frontlet:Age nommée pour un âge entier."""
    if is_missing(age_value):
        return None
    try:
        age_num = int(float(str(age_value).strip()))
    except Exception:
        return None
    age_uri = DATA[f"ue_sud_Age_{node_suffix}"]
    g.add((age_uri, RDF.type, F.Age))
    g.add((age_uri, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    g.add((age_uri, RDFS.label, Literal(f"{age_num} years old", lang="en")))
    return age_uri


def create_age_interval_node(g, age_value, node_suffix):
    """Ressource frontlet:AgeInterval nommée pour un âge estimé / une fourchette."""
    if is_missing(age_value):
        return None
    label = str(age_value).strip()
    age_uri = DATA[f"ue_sud_AgeInterval_{node_suffix}"]
    g.add((age_uri, RDF.type, F.AgeInterval))
    g.add((age_uri, RDFS.label, Literal(label)))
    g.add((age_uri, SKOS.prefLabel, Literal(label)))
    return age_uri


# --------------------- Cause décès --------------------
def find_thesaurus_term_by_prefLabel_fr(g, label_fr):
    if label_fr is None or str(label_fr).strip() == "":
        return None
    for s, p, o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == norm(label_fr):
            return s
    for s, p, o in g.triples((None, RDFS.label, None)):
        if norm(o) == norm(label_fr):
            return s
    return None


def load_death_cause_thesaurus(g):
    cause_map = {}
    try:
        for cause_uri in g.subjects(RDF.type, T.DeathCause):
            for label_obj in g.objects(cause_uri, SKOS.prefLabel):
                if label_obj.language in ("fr", None):
                    label_norm = norm(str(label_obj))
                    if label_norm:
                        cause_map[label_norm] = cause_uri
        print(f"Loaded {len(cause_map)} DeathCause entries from thesaurus")
    except Exception as e:
        print(f"Warning: Could not load DeathCause thesaurus: {e}")
    return cause_map


def load_death_nature_thesaurus(g):
    nature_map = {}
    try:
        for nature_uri in g.subjects(RDF.type, T.DeathNature):
            for label_obj in g.objects(nature_uri, SKOS.prefLabel):
                if label_obj.language in ("fr", None):
                    label_norm = norm(str(label_obj))
                    if label_norm:
                        nature_map[label_norm] = nature_uri
        print(f"Loaded {len(nature_map)} DeathNature entries from thesaurus")
    except Exception as e:
        print(f"Warning: Could not load DeathNature thesaurus: {e}")
    return nature_map


def load_mapping_csv(mapping_path):
    mapping_cause = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping_cause, mapping_nature
    try:
        mdf = None
        encodings_to_try = ["utf-8", "utf-8-sig", "cp1252", "latin-1"]
        for enc in encodings_to_try:
            try:
                mdf = pd.read_csv(mapping_path, sep=";", dtype=str, encoding=enc)
                break
            except UnicodeDecodeError:
                continue
        if mdf is None:
            with open(mapping_path, "rb") as fh:
                raw = fh.read().decode("utf-8", errors="replace")
            from io import StringIO
            mdf = pd.read_csv(StringIO(raw), sep=";", dtype=str)

        columns_by_norm = {norm(c): c for c in mdf.columns}
        src_col = columns_by_norm.get("ue_sud")
        thes_col = columns_by_norm.get("thesaurus")
        nature_col = columns_by_norm.get("nature")

        if src_col is None or thes_col is None:
            print(
                "Warning: mapping CSV must contain columns 'UE_Sud' and 'Thesaurus'. "
                "Will use direct matching only."
            )
            return mapping_cause, mapping_nature

        for _, r in mdf.iterrows():
            source_key = norm(r.get(src_col, ""))
            thesaurus_val = str(r.get(thes_col, "")).strip()

            if source_key and not is_missing(thesaurus_val):
                mapping_cause[source_key] = thesaurus_val

            if nature_col is not None:
                nature_val = str(r.get(nature_col, "")).strip()
                if source_key and not is_missing(nature_val):
                    mapping_nature[source_key] = nature_val

        print(
            f"Loaded {len(mapping_cause)} UE_Sud->Thesaurus mappings from CSV"
            f" and {len(mapping_nature)} UE_Sud->Nature mappings"
        )
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping_cause, mapping_nature


def match_death_cause(value, mapping_dict, thesaurus_map):
    if not value or is_missing(value):
        return None, None, False

    val_norm = norm(value)

    mapped_label = mapping_dict.get(val_norm)
    if mapped_label:
        uri = thesaurus_map.get(norm(mapped_label))
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


def create_or_get_concept_instance(graph, class_uri, key_prefix, label, thesaurus_uri=None):
    if is_missing(label):
        return None
    label_text = str(label).strip()
    inst_uri = DATA[f"{key_prefix}_{slug(label_text) or 'unknown'}"]
    if (inst_uri, RDF.type, class_uri) not in graph:
        graph.add((inst_uri, RDF.type, class_uri))
    if (inst_uri, RDFS.label, None) not in graph:
        graph.add((inst_uri, RDFS.label, Literal(label_text)))
    if thesaurus_uri is not None:
        graph.add((inst_uri, SKOS.closeMatch, thesaurus_uri))
    return inst_uri


# Mots-cles narratifs indiquant des evenements de controle/repatriation.
CONTROL_KEYWORDS = (
    "intercept",
    "checkpoint",
    "detained",
    "detain",
)
REPATRIATION_KEYWORDS = ("repatri",)


def contains_any_keyword(value, keywords):
    text = norm(value)
    return bool(text) and any(keyword in text for keyword in keywords)


def build_tagged_comment(row, columns):
    parts = []
    for column in columns:
        value = row.get(column, "")
        if not is_missing(value):
            parts.append(f"{column}: {str(value).strip()}")
    return "; ".join(parts)


def infer_death_nature_from_causes(primary_cause, secondary_cause):
    text = norm(f"{primary_cause or ''} {secondary_cause or ''}")
    if text == "":
        return None

    suicide_keywords = (
        "suicide",
        "self-inflicted",
        "self inflicted",
        "auto-inflicted",
    )
    homicide_keywords = (
        "homicide",
        "murder",
        "killed by",
        "shot",
        "beaten",
        "assault",
    )
    accident_keywords = (
        "accident",
        "collision",
        "crash",
        "drowning",
        "asphyxia",
        "hypothermia",
        "fall",
    )

    if any(k in text for k in suicide_keywords):
        return "suicide"
    if any(k in text for k in homicide_keywords):
        return "homicide"
    if any(k in text for k in accident_keywords):
        return "accident"
    return None


def create_individual_event(
    g,
    person_uri,
    event_uri,
    event_class,
    related_event_uri=None,
    relation_to_related=None,
    comment=None,
    narrative=None,
    country_uri=None,
    target_country_uri=None,
    how_long_dead=None,
):
    g.add((event_uri, RDF.type, event_class))
    g.add((event_uri, RDF.type, F.IndividualEvent))
    g.add((person_uri, PROP_composedOf, event_uri))

    if related_event_uri is not None:
        if relation_to_related == "after":
            g.add((related_event_uri, PROP_temporal_before, event_uri))
            g.add((event_uri, PROP_temporal_after, related_event_uri))
        elif relation_to_related == "before":
            g.add((event_uri, PROP_temporal_before, related_event_uri))
            g.add((related_event_uri, PROP_temporal_after, event_uri))

    if comment and not is_missing(comment):
        g.add((event_uri, PROP_hasComment, Literal(str(comment).strip())))
    if narrative and not is_missing(narrative):
        g.add((event_uri, PROP_hasNarrative, Literal(str(narrative).strip())))
    if country_uri is not None:
        g.add((event_uri, F.countrydeath, country_uri))
    if target_country_uri is not None:
        g.add((event_uri, PROP_targetCountry, target_country_uri))
    if how_long_dead and not is_missing(how_long_dead):
        g.add((event_uri, PROP_howLongDead, Literal(str(how_long_dead).strip())))

    return event_uri


# ----------------- Chargement des graphes ----------------
g_ref = Graph()
g_ref.parse(ONTO_PATH, format="turtle")
g_ref.parse(THES_PATH, format="turtle")

g = Graph()
g.bind("frontlet",      F)
g.bind("frontlet_data", DATA)
g.bind("thes",          T)
g.bind("skos",          SKOS)
g.bind("rdfs",          RDFS)
g.bind("rdf",           RDF)
g.bind("geo",           GEO)
g.bind("time",          TIME)
g.bind("temp",          TEMP)

copy_all_class_hierarchy(g_ref, g)

thesaurus_map = load_death_cause_thesaurus(g_ref)
nature_thesaurus_map = load_death_nature_thesaurus(g_ref)
mapping_dict, mapping_nature = load_mapping_csv(MAPPING_PATH)

# Propriétés
PERSON_CLASS        = find_by_label(g_ref, "Person")       or F.Person
DEATH_EVENT_CLASS   = find_by_label(g_ref, "Death")        or F.Death
CORPSE_ANALYSIS_CLASS = find_by_label(g_ref, "Corpse analysis") or F.CorpseAnalysis
CONTROL_EVENT_CLASS = find_by_label(g_ref, "Control") or F.Control
CORPSE_REPATRIATION_CLASS = find_by_label(g_ref, "Corpse repatriation") or F.CorpseRepatriation
INHUMATION_EVENT_CLASS = find_by_label(g_ref, "Inhumation") or F.Inhumation
PROP_composedOf     = find_by_label(g_ref, "composedOf")   or F.composedOf
PROP_birthPlace     = find_by_label(g_ref, "birth place")  or F.birthPlace
PROP_hasAgeLink     = find_by_label(g_ref, "aged")         or F.aged
PROP_hasDeathCause  = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "hasDeathNature") or find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_sourcedBy      = find_by_label(g_ref, "sourcedBy")    or F.sourcedBy
PROP_certificate    = find_by_label(g_ref, "certificate")  or F.certificate
PROP_hasAuthority   = find_by_label(g_ref, "has an implicated authority") or F.hasAuthority
PROP_hasComment     = find_by_label(g_ref, "hasComment")   or F.hasComment
PROP_hasNarrative   = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_targetCountry  = find_by_label(g_ref, "target country") or F.targetCountry
PROP_hasType        = find_by_label(g_ref, "has type") or F.hasType
PROP_howLongDead    = find_by_label(g_ref, "how long dead") or F.howLongDead
PROP_temporal_before = find_by_label(g_ref, "before")      or TEMP.before
PROP_temporal_after  = find_by_label(g_ref, "after")       or TEMP.after
PROP_gender         = find_by_label(g_ref, "has gender")   or F.hasGender
DEATH_CAUSE_CLASS   = F.DeathCause
DEATH_NATURE_CLASS  = F.DeathNature

if (PROP_howLongDead, RDF.type, None) not in g:
    g.add((PROP_howLongDead, RDF.type, OWL.DatatypeProperty))
    g.add((PROP_howLongDead, RDFS.label, Literal("how long dead", lang="en")))

THES_male   = T.male
THES_female = T.female
THES_human  = T.human

# Instances frontlet:Gender (comme IOM)
GENDER_MALE_URI    = DATA["ue_sud_Gender_male"]
GENDER_FEMALE_URI  = DATA["ue_sud_Gender_female"]
GENDER_UNKNOWN_URI = DATA["ue_sud_Gender_unknown"]
for _guri, _glabel, _gthes in [
    (GENDER_MALE_URI,    "male",    THES_male),
    (GENDER_FEMALE_URI,  "female",  T.female),
    (GENDER_UNKNOWN_URI, "unknown", None),
]:
    g.add((_guri, RDF.type, F.Gender))
    g.add((_guri, RDFS.label, Literal(_glabel, lang="en")))
    if _gthes is not None:
        g.add((_guri, SKOS.exactMatch, _gthes))

# Ressource partagée pour garder un lien Age même si la source est vide
AGE_UNKNOWN_URI = DATA["ue_sud_Age_unknown"]
g.add((AGE_UNKNOWN_URI, RDF.type, F.AgeInterval))
g.add((AGE_UNKNOWN_URI, RDFS.label, Literal("unknown", lang="en")))
g.add((AGE_UNKNOWN_URI, SKOS.prefLabel, Literal("unknown", lang="en")))

ADDITIONAL_EVENT_SPECS = build_additional_event_specs(
    g_ref,
    F,
    find_by_label,
    exclude_names=["Inhumation", "Control", "CorpseRepatriation", "Injury", "CorpseAnalysis"],
)

# Nœuds Certainty (3 niveaux)
CERTAINTY_URIS = {}
for _n in (1, 2, 3):
    _uri = DATA[f"ue_sud_Certainty_{_n}"]
    g.add((_uri, RDF.type, F.Certainty))
    CERTAINTY_URIS[str(_n)] = _uri

# -------------------- Lecture du CSV --------------------
encodings_to_try = ["utf-8", "utf-8-sig", "cp1252", "latin-1"]
df = None
for _enc in encodings_to_try:
    try:
        df = pd.read_csv(
            CSV_PATH, sep=";", engine="python", dtype=str,
            keep_default_na=False, na_values=["", "NaN", "nan"],
            encoding=_enc,
        )
        break
    except UnicodeDecodeError:
        continue
if df is None:
    with open(CSV_PATH, "rb") as fh:
        raw = fh.read().decode("utf-8", errors="replace")
    from io import StringIO
    df = pd.read_csv(StringIO(raw), sep=";", engine="python", dtype=str,
                     keep_default_na=False, na_values=["", "NaN", "nan"])

# Supprimer les colonnes Unnamed
df = df[[c for c in df.columns if not c.startswith("Unnamed")]]

print(f"CSV chargé : {len(df)} lignes, {len(df.columns)} colonnes.")

if ROW_LIMIT is not None and ROW_LIMIT > 0:
    df = df.head(ROW_LIMIT).copy()
    print(f"Mode compat activé: traitement limité à {len(df)} lignes.")

# ------------------- Traitement des lignes ----------------
count_person           = 0
count_death_events     = 0
count_cause_matched    = 0
count_cause_literal    = 0
count_sources          = 0
count_certificates     = 0
count_control_events   = 0
count_corpse_analysis  = 0
count_inhumation       = 0
count_repatriation     = 0
count_collective_events = 0
count_geocode_success  = 0
count_geocode_failed   = 0
count_death_nature     = 0
count_additional_typed_events = 0

created_collective_events = {}
geocode_cache = load_geocode_cache(GEOCODE_CACHE_PATH)

for idx, row in df.iterrows():
    row_num = idx + 1  # indexe a partir de 1

    person_uri = DATA[f"ue_sud_Person_{row_num}"]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1

    # ---- GENRE ----
    sex_val = str(row.get("Sex", "") or "").strip().lower()
    if sex_val in ("male", "m", "homme"):
        g.set((person_uri, PROP_gender, GENDER_MALE_URI))
    elif sex_val in ("female", "f", "femme"):
        g.set((person_uri, PROP_gender, GENDER_FEMALE_URI))
    else:
        g.set((person_uri, PROP_gender, GENDER_UNKNOWN_URI))

    # ---- ÂGE ----
    age_val  = row.get("Age", "")
    est_age  = row.get("Estimated_age", "")

    age_node = None
    if not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
        age_node = create_age_node(g, age_val, row_num)
    elif not is_missing(est_age):
        age_node = create_age_interval_node(g, est_age, row_num)
    elif not is_missing(age_val):
        # valeur non-entière (ex. "25-30") → AgeInterval
        age_node = create_age_interval_node(g, age_val, row_num)

    if age_node is None:
        age_node = AGE_UNKNOWN_URI
    g.add((person_uri, PROP_hasAgeLink, age_node))

    # ---- NATIONALITÉ (pays d'origine) ----
    nationality = row.get("Stated_nationality", "") or row.get("Guessed_nationality", "")
    birth_country = None
    if not is_missing(nationality):
        birth_country = ensure_country_node(g, nationality)
    if birth_country:
        g.add((person_uri, PROP_birthPlace, birth_country))

    # ---- COMMENTAIRE (apparence, ethnicity) ----
    comment_parts = []
    for col in ("Descriptions_of_race/ethnicity", "Features", "Personal_items"):
        v = row.get(col, "")
        if v and not is_missing(v):
            comment_parts.append(str(v).strip())
    if comment_parts:
        g.add((person_uri, PROP_hasComment, Literal("; ".join(comment_parts))))
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Details_of_incident", "Circumstances", "Other_information", "Primary_cause", "Secondary_cause"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Where buried", "Judicial_authority", "City/Town/Village", "Country"], is_missing))

    # ---- ÉVÉNEMENT DÉCÈS ----
    event_uri = DATA[f"ue_sud_Death_{row_num}"]
    g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
    g.add((event_uri, RDF.type, F.IndividualEvent))
    g.add((person_uri, PROP_composedOf, event_uri))
    count_death_events += 1

    # ---- DURÉE AVANT DÉCOUVERTE ----
    how_long_dead = row.get("How_long_dead", "")
    if not is_missing(how_long_dead):
        g.add((event_uri, PROP_howLongDead, Literal(str(how_long_dead).strip())))

    # ---- DATE DE DÉCÈS ----
    day   = str(row.get("Day_died",   "") or "").strip()
    month = str(row.get("Month_died", "") or "").strip()
    year  = str(row.get("Year_died",  "") or "").strip()
    if day and month and year and re.match(r"^\d+$", day) and re.match(r"^\d+$", month) and re.match(r"^\d{4}$", year):
        date_str = f"{day.zfill(2)}/{month.zfill(2)}/{year}"
        g.add((event_uri, TIME.inXSDDate, Literal(date_str)))
        weekday_name = infer_day_of_week_name(date_str)
        if weekday_name:
            g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
            g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
            g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))

    # ---- PAYS OÙ LE DÉCÈS A EU LIEU ----
    country_val = row.get("Country", "")
    if not is_missing(country_val):
        country_uri = ensure_country_node(g, country_val)
        if country_uri:
            g.add((event_uri, F.countrydeath, country_uri))
    else:
        country_uri = None

    # ---- CAUSE DE DÉCÈS ----
    # Règle stricte: clé UE_Sud = Primary_cause ; valeur utilisée = Thesaurus.
    primary   = row.get("Primary_cause",   "") or ""
    secondary = row.get("Secondary_cause", "") or ""

    if primary and not is_missing(primary):
        mapped_cause_label = mapping_dict.get(norm(primary), "")
        if not is_missing(mapped_cause_label):
            mapped_cause_label = str(mapped_cause_label).strip()
            cause_thes_uri = thesaurus_map.get(norm(mapped_cause_label))
            cause_instance = create_or_get_concept_instance(
                g,
                DEATH_CAUSE_CLASS,
                "ue_sud_DeathCause",
                mapped_cause_label,
                thesaurus_uri=cause_thes_uri,
            )
            if cause_instance is not None:
                g.add((event_uri, PROP_hasDeathCause, cause_instance))
                if cause_thes_uri is not None:
                    count_cause_matched += 1
                else:
                    count_cause_literal += 1

    # ---- NATURE DU DÉCÈS ----
    # Règle stricte: clé UE_Sud = Primary_cause ; valeur utilisée = Nature.
    nature_val = mapping_nature.get(norm(primary or ""), "")
    if not is_missing(nature_val):
        nature_label = str(nature_val).strip()
        nature_thes_uri = nature_thesaurus_map.get(norm(nature_label))
        nature_instance = create_or_get_concept_instance(
            g,
            DEATH_NATURE_CLASS,
            "ue_sud_DeathNature",
            nature_label,
            thesaurus_uri=nature_thes_uri,
        )
        if nature_instance is not None:
            g.add((event_uri, PROP_hasDeathNature, nature_instance))
            count_death_nature += 1

    # ---- CERTITUDE ----
    certainty_val = str(row.get("Certainty", "") or "").strip()
    if certainty_val in CERTAINTY_URIS:
        g.add((event_uri, F.hasCertainty, CERTAINTY_URIS[certainty_val]))

    # ---- MODE DE TRANSPORT ----
    route_val = str(row.get("Route", "") or row.get("Migration route", "") or "").strip().lower()
    transport_context = " ".join(
        [
            route_val,
            str(row.get("Primary_cause", "") or "").strip().lower(),
            str(row.get("Secondary_cause", "") or "").strip().lower(),
            str(row.get("Circumstances", "") or "").strip().lower(),
            str(row.get("Details_of_incident", "") or "").strip().lower(),
        ]
    )
    if any(k in transport_context for k in ("land", "overland", "on foot", "foot", "pied", "terre", "walk", "desert")):
        g.add((event_uri, F.transportMode, THES_human))
    elif any(k in transport_context for k in ("drown", "drowning", "boat", "ship", "vessel", "ferry", "raft", "sea", "mediterranean")):
        g.add((event_uri, F.transportMode, T.boat))
    elif any(k in transport_context for k in ("truck", "lorry", "vehicle", "car", "van", "bus", "train", "rail")):
        g.add((event_uri, F.transportMode, T.landVehicle))

    # ---- SOURCES & CERTIFICATS ----
    has_death_cert  = norm(row.get("Death_certificate",  "") or "") in ("yes", "oui", "1")
    has_cemetery    = norm(row.get("Cemetery_register",  "") or "") in ("yes", "oui", "1")
    has_coroner     = norm(row.get("Coroner_archive",     "") or "") in ("yes", "oui", "1")
    has_other_docs  = norm(row.get("Other_documents",     "") or "") in ("yes", "oui", "1")

    has_any_source = has_death_cert or has_cemetery or has_coroner or has_other_docs

    if has_death_cert:
        cert_uri = DATA[f"DeathCertificate_{row_num}"]
        g.add((cert_uri, RDF.type, F.DeathCertificate))
        if not is_missing(how_long_dead):
            g.add((cert_uri, PROP_howLongDead, Literal(str(how_long_dead).strip())))
        g.add((event_uri, PROP_certificate, cert_uri))
        count_certificates += 1

    if has_any_source:
        source_uri = DATA[f"ue_sud_Source_{row_num}"]
        g.add((source_uri, RDF.type, F.Source))
        if has_death_cert:
            g.add((source_uri, RDF.type, F.DeathCertificate))
        if has_coroner or has_other_docs or has_cemetery:
            g.add((source_uri, RDF.type, F.OtherOfficialDocument))
        g.add((event_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

    # ---- ÉVÉNEMENTS INDIVIDUELS COMPLÉMENTAIRES ----
    # Le deces reste l'evenement principal pour ce jeu de donnees.
    # La creation de CorpseAnalysis est volontairement desactivee pour eviter une sur-representation.

    control_narratives = []
    for control_col in ("Details_of_incident", "Circumstances"):
        control_value = row.get(control_col, "")
        if contains_any_keyword(control_value, CONTROL_KEYWORDS):
            control_narratives.append(str(control_value).strip())
    if control_narratives:
        control_uri = DATA[f"ue_sud_Control_{row_num}"]
        trigger_str = "; ".join(
            str(row.get(col, "")).strip()
            for col in ("Details_of_incident", "Circumstances")
            if contains_any_keyword(row.get(col, ""), CONTROL_KEYWORDS)
        )
        authority_val = str(row.get("Judicial_authority", "")).strip()
        control_comment = f"[Contrôle : {trigger_str}]" + ("; " + authority_val if not is_missing(authority_val) else "")
        create_individual_event(
            g,
            person_uri,
            control_uri,
            CONTROL_EVENT_CLASS,
            related_event_uri=event_uri,
            relation_to_related="before",
            comment=control_comment,
            narrative="; ".join(control_narratives),
            country_uri=country_uri,
            how_long_dead=how_long_dead,
        )
        authority = row.get("Judicial_authority", "")
        if not is_missing(authority):
            g.add((control_uri, PROP_hasAuthority, Literal(str(authority).strip())))
        count_control_events += 1

    # ---- ÉVÉNEMENT COLLECTIF (Incident_number) ----
    incident_val = str(row.get("Incident_number", "") or "").strip()
    city_val     = str(row.get("City/Town/Village", "") or "").strip()
    if incident_val and not is_missing(incident_val):
        city_slug = slug(city_val) if not is_missing(city_val) else "unknown"
        incident_slug = slug(incident_val)
        if incident_slug == "":
            incident_slug = "unknown"
        collective_key = f"{city_slug}_{incident_slug}"
        collective_uri = DATA[f"ue_sud_CollectiveEvent_{collective_key}"]
        is_new_collective = str(collective_uri) not in created_collective_events
        if is_new_collective:
            g.add((collective_uri, RDF.type, F.CollectiveEvent))
            created_collective_events[str(collective_uri)] = collective_uri
            count_collective_events += 1
        g.add((event_uri, F.group, collective_uri))

        details = row.get("Details_of_incident", "")
        if details and not is_missing(details) and is_new_collective:
            g.add((collective_uri, PROP_hasNarrative, Literal(str(details).strip())))

    # ---- GÉOCODAGE (City/Town/Village + Country) ----
    geo_query = None
    if not is_missing(city_val):
        country_name = row.get("Country", "")
        if not is_missing(country_name):
            geo_query = f"{city_val}, {country_name}"
        else:
            geo_query = city_val

    if ENABLE_GEOCODING and geo_query:
        lat_f, lon_f = geocode_location(geo_query, geocode_cache)
        if lat_f is not None and lon_f is not None and math.isfinite(float(lat_f)) and math.isfinite(float(lon_f)):
            wkt = f"POINT({float(lon_f)} {float(lat_f)})"
            geom_uri = DATA[f"ue_sud_geometry_{row_num}"]
            g.add((event_uri, GEO.hasGeometry, geom_uri))
            g.add((geom_uri, RDF.type, GEO.Geometry))
            g.add((geom_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
            count_geocode_success += 1
        else:
            count_geocode_failed += 1

    # ---- INHUMATION (Lieu d'enterrement / Cemetery_register) ----
    where_buried = row.get("Where buried", "") or row.get("Where_buried", "") or ""
    is_repatriated = contains_any_keyword(where_buried, REPATRIATION_KEYWORDS)

    if is_repatriated:
        repatriation_uri = DATA[f"ue_sud_CorpseRepatriation_{row_num}"]
        extra_vals = "; ".join(
            str(row.get(col, "")).strip()
            for col in ("Date_burial_authorised", "Date_buried")
            if not is_missing(row.get(col, ""))
        )
        repatriation_comment = f"[Rapatriement du corps : {where_buried.strip()}]" + ("; " + extra_vals if extra_vals else "")
        create_individual_event(
            g,
            person_uri,
            repatriation_uri,
            CORPSE_REPATRIATION_CLASS,
            related_event_uri=event_uri,
            relation_to_related="after",
            comment=repatriation_comment,
            country_uri=country_uri,
            target_country_uri=birth_country,
            how_long_dead=how_long_dead,
        )
        count_repatriation += 1

    trigger_inhumation = ((not is_missing(where_buried)) and not is_repatriated) or has_cemetery

    if trigger_inhumation:
        inhumation_uri = DATA[f"InhumationEvent_{row_num}"]
        inhumation_triggers = []
        if not is_missing(where_buried) and not is_repatriated:
            inhumation_triggers.append(where_buried.strip())
        if has_cemetery:
            inhumation_triggers.append("registre du cimetière")
        extra_vals = "; ".join(
            str(row.get(col, "")).strip()
            for col in ("Date_burial_authorised", "Date_buried")
            if not is_missing(row.get(col, ""))
        )
        inhumation_comment = f"[Inhumation : {'; '.join(inhumation_triggers)}]" + ("; " + extra_vals if extra_vals else "")
        create_individual_event(
            g,
            person_uri,
            inhumation_uri,
            INHUMATION_EVENT_CLASS,
            related_event_uri=event_uri,
            relation_to_related="after",
            comment=inhumation_comment,
            country_uri=country_uri,
            how_long_dead=how_long_dead,
        )
        g.add((inhumation_uri, T.missingAfterTakingOver, event_uri))

        if ENABLE_GEOCODING and not is_missing(where_buried):
            inhumation_lat, inhumation_lon = geocode_location(
                f"{where_buried}, {row.get('Country', '')}".strip(", "),
                geocode_cache,
            )
            if inhumation_lat is not None and inhumation_lon is not None:
                if math.isfinite(float(inhumation_lat)) and math.isfinite(float(inhumation_lon)):
                    wkt_inh = f"POINT({float(inhumation_lon)} {float(inhumation_lat)})"
                    geom_inh_uri = DATA[f"ue_sud_geometry_inhumation_{row_num}"]
                    g.add((inhumation_uri, GEO.hasGeometry, geom_inh_uri))
                    g.add((geom_inh_uri, RDF.type, GEO.Geometry))
                    g.add((geom_inh_uri, GEO.asWKT, Literal(wkt_inh, datatype=GEO.wktLiteral)))

        count_inhumation += 1

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, event_uri)],
        collective_uri if incident_val and not is_missing(incident_val) else None,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "ue_sud",
        row_num,
        F,
        RDF,
        Literal,
        PROP_composedOf,
        F.group,
        PROP_temporal_before,
        PROP_temporal_after,
        PROP_hasComment,
        PROP_hasNarrative,
    )
    count_additional_typed_events += sum(additional_counts.values())

# --------------------- Resume et sortie ------------------
# Nettoyage strict: supprimer toute instance Injury et les liens associes.
injury_nodes = set(g.subjects(RDF.type, F.Injury))
for _inj in injury_nodes:
    for _person in list(g.subjects(PROP_composedOf, _inj)):
        g.remove((_person, PROP_composedOf, _inj))
    for _s, _p, _o in list(g.triples((_inj, None, None))):
        g.remove((_s, _p, _o))
    for _s, _p, _o in list(g.triples((None, None, _inj))):
        g.remove((_s, _p, _o))

# Nettoyage de securite: conserver uniquement les liens `countrydeath` dans les donnees exportees.
for _s, _p, _o in list(g.triples((None, F.country, None))):
    g.remove((_s, _p, _o))

g.serialize(destination=OUTPUT_TTL, format="turtle")
save_geocode_cache(GEOCODE_CACHE_PATH, geocode_cache)

print("\n" + "=" * 60)
print("Import UE Sud (southern_eu) complete.")
print("=" * 60)
print(f"Rows processed (persons)    : {count_person}")
print(f"Death events created        : {count_death_events}")
print(f"Collective events created   : {count_collective_events}")
print(f"Certificates created        : {count_certificates}")
print(f"Sources created             : {count_sources}")
print(f"Corpse analysis events      : {count_corpse_analysis}")
print(f"Control events created      : {count_control_events}")
print(f"Inhumation events created   : {count_inhumation}")
print(f"Repatriation events created : {count_repatriation}")
print(f"Other typed events created  : {count_additional_typed_events}")
print()
print("Cause décès - mapping thesaurus :")
print(f"  - Matched to thesaurus URI : {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"  - DeathNature linked : {count_death_nature}")
print()
print("Géocodage :")
print(f"  - Réussis   : {count_geocode_success}")
print(f"  - Non résolus: {count_geocode_failed}")
print(f"  - Rate limit : {'oui' if GEOCODER_RATE_LIMITED else 'non'}")
print("=" * 60)
print(f"Output written to: {OUTPUT_TTL}")


