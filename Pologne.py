#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV Alpes → ontologie RDF selon vos règles.
Amélioration du mapping Cause_deces avec le thésaurus DeathCause (prefLabel@fr)
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
CSV_PATH = "pologne/pologne.csv"
OUTPUT_TTL = "pologne/frontlet_import_output.ttl"
MAPPING_PATH = "pologne/mappingPologneThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)

# Espaces de noms par defaut
F = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")

# ----------------- Fonctions utilitaires ----------------
def norm(s):
    """normalize string for comparisons"""
    if s is None:
        return ""
    s = str(s).strip()
    s = unicodedata.normalize("NFKD", s)
    s = re.sub(r"\s+", " ", s)
    return s.lower()

def is_missing(s):
    """Return True for None/empty or common null tokens like 'nan', 'none', 'n/a'."""
    if s is None:
        return True
    s_norm = norm(s)
    if s_norm == "":
        return True
    if s_norm in ("nan", "none", "n/a", "na", "-"):
        return True
    return False

def find_by_label(g, search, props=(RDFS.label, SKOS.prefLabel)):
    """Return first subject in graph whose label/prefLabel matches `search` (case-insensitive)."""
    if search is None or str(search).strip() == "":
        return None
    s_norm = norm(search)
    for p in props:
        for s,_,o in g.triples((None, p, None)):
            if norm(o) == s_norm:
                return s
    # try contains (looser)
    for p in props:
        for s,_,o in g.triples((None, p, None)):
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


def get_first_non_missing_row_value(row, exact_names=None, header_keywords=None):
    """
    Return first non-missing row value using exact column names, then fallback
    to columns whose header contains one of the provided keywords.
    """
    exact_names = exact_names or []
    header_keywords = [k.lower() for k in (header_keywords or [])]

    for name in exact_names:
        value = row.get(name, "")
        if not is_missing(value):
            return value

    if header_keywords:
        for col in row.index:
            col_l = str(col).lower()
            if any(k in col_l for k in header_keywords):
                value = row.get(col, "")
                if not is_missing(value):
                    return value

    return ""

# Initialiser le géocodeur
geolocator = Nominatim(user_agent="frontlet_alpes_geocoder")
location_geocode_cache = {}
MAX_GEOCODING_CALLS = 20
_geocoding_call_count = 0

POLISH_COUNTRY_TO_ISO2 = {
    "polska": "PL",
    "niemcy": "DE",
    "francja": "FR",
    "hiszpania": "ES",
    "wlochy": "IT",
    "grecja": "GR",
    "belgia": "BE",
    "holandia": "NL",
    "niderlandy": "NL",
    "szwajcaria": "CH",
    "austria": "AT",
    "weggry": "HU",
    "czechy": "CZ",
    "slowacja": "SK",
    "litwa": "LT",
    "lotwa": "LV",
    "estonia": "EE",
    "norwegia": "NO",
    "szwecja": "SE",
    "dania": "DK",
    "finlandia": "FI",
    "irlandia": "IE",
    "portugalia": "PT",
    "rumunia": "RO",
    "bulgaria": "BG",
    "chorwacja": "HR",
    "slowenia": "SI",
    "serbia": "RS",
    "bośnia i hercegowina": "BA",
    "bosnia i hercegowina": "BA",
    "czarnogora": "ME",
    "albania": "AL",
    "macedonia polnocna": "MK",
    "kosowo": "XK",
    "ukraina": "UA",
    "bialorus": "BY",
    "moldawia": "MD",
    "rosja": "RU",
    "turcja": "TR",
    "syria": "SY",
    "irak": "IQ",
    "iran": "IR",
    "afganistan": "AF",
    "pakistan": "PK",
    "bangladesz": "BD",
    "indie": "IN",
    "sri lanka": "LK",
    "nepal": "NP",
    "myanmar": "MM",
    "wietnam": "VN",
    "chiny": "CN",
    "egipt": "EG",
    "libia": "LY",
    "tunezja": "TN",
    "algieria": "DZ",
    "maroko": "MA",
    "sudan": "SD",
    "erytrea": "ER",
    "etiopia": "ET",
    "somalia": "SO",
    "nigeria": "NG",
    "ghana": "GH",
    "gwinea": "GN",
    "wybrzeze kosci sloniowej": "CI",
    "kamerun": "CM",
    "senegal": "SN",
    "mali": "ML",
    "niger": "NE",
}


def country_from_polish_name(value):
    """Resolve country from common Polish names/aliases to a pycountry record."""
    if is_missing(value):
        return None

    text = str(value)
    candidates = [text]
    candidates.extend(re.split(r"[,;/]|\boraz\b|\bi\b|\band\b", text, flags=re.IGNORECASE))

    for candidate in candidates:
        candidate_norm = norm(candidate)
        candidate_norm = re.sub(r"\(.*?\)", "", candidate_norm).strip()
        candidate_norm = re.sub(r"^obywatelstwo\s+", "", candidate_norm).strip()
        candidate_norm = re.sub(r"\s+", " ", candidate_norm)
        if not candidate_norm:
            continue

        iso2 = POLISH_COUNTRY_TO_ISO2.get(candidate_norm)
        if iso2:
            cc = pycountry.countries.get(alpha_2=iso2)
            if cc:
                return cc

    return None

def geocode_location(location_name, max_retries=3):
    """
    Géocode un nom de lieu et retourne (latitude, longitude) ou (None, None).
    Cherche d'abord un cimetière, sinon utilise le centroïde de la ville.
    """
    global _geocoding_call_count
    if _geocoding_call_count >= MAX_GEOCODING_CALLS:
        return None, None
    _geocoding_call_count += 1
    if is_missing(location_name):
        return None, None
    
    location_str = str(location_name).strip()
    
    # Étape 1 : Chercher un cimetière dans la ville
    for attempt in range(max_retries):
        try:
            cemetery_query = f"cemetery {location_str}"
            results = geolocator.geocode(cemetery_query, exactly_one=False, limit=5, timeout=10)
            
            if results:
                # Vérifier s'il y a exactement un cimetière
                cemetery_results = [r for r in results if 'cemetery' in r.address.lower() or 'cimetière' in r.address.lower() or 'cementerio' in r.address.lower()]
                
                if len(cemetery_results) == 1:
                    # Un seul cimetière trouvé, on l'utilise
                    return cemetery_results[0].latitude, cemetery_results[0].longitude
            
            # Si pas de cimetière unique, chercher le centroïde de la ville
            location = geolocator.geocode(location_str, timeout=10)
            if location:
                return location.latitude, location.longitude
            else:
                return None, None
                
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                time.sleep(1)
                continue
            else:
                print(f"Géocodage timeout pour: {location_name}")
                return None, None
        except GeocoderServiceError as e:
            print(f"Erreur de géocodage pour {location_name}: {e}")
            return None, None
        except Exception as e:
            print(f"Erreur inattendue lors du géocodage de {location_name}: {e}")
            return None, None
    
    return None, None


def geocode_event_location(location_name, max_retries=3):
    """
    Geocode death location text (Lokalizacja/Location) and return
    (latitude, longitude) or (None, None).
    """
    if is_missing(location_name):
        return None, None

    location_str = re.sub(r"\s+", " ", str(location_name)).strip()
    if not location_str:
        return None, None

    cache_key = norm(location_str)
    if cache_key in location_geocode_cache:
        return location_geocode_cache[cache_key]

    for attempt in range(max_retries):
        try:
            time.sleep(1)
            loc = geolocator.geocode(location_str, timeout=10)
            if loc:
                coords = (loc.latitude, loc.longitude)
                location_geocode_cache[cache_key] = coords
                return coords
            location_geocode_cache[cache_key] = (None, None)
            return None, None
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                continue
            print(f"Géocodage timeout pour lieu de décès: {location_name}")
        except GeocoderServiceError as e:
            print(f"Erreur de géocodage pour lieu de décès {location_name}: {e}")
            break
        except Exception as e:
            print(f"Erreur inattendue lors du géocodage du lieu de décès {location_name}: {e}")
            break

    location_geocode_cache[cache_key] = (None, None)
    return None, None

def is_suspicious_coordinate(lat, lon):
    """
    Vérifie si les coordonnées sont suspectes et doivent être ignorées.
    Retourne (is_suspicious: bool, reason: str)
    """
    try:
        lat = float(lat)
        lon = float(lon)
    except:
        return True, "PARSE_ERROR"
    
    # Coordonnées -99, -99 (valeur par défaut d'erreur)
    if lon == -99 and lat == -99:
        return True, "ERROR_-99,-99"
    
    # Nord-Ouest de Madagascar (lat -12 à -14, lon 43 à 45)
    if -14 < lat < -12 and 43 < lon < 45:
        return True, "Madagascar_NW"
    
    # Vers le Pôle Nord (lat > 70)
    if lat > 70:
        return True, "High_North"
    
    # Hors limites (|lon| > 180 ou |lat| > 90)
    if abs(lon) > 180 or abs(lat) > 90:
        return True, "OUT_OF_BOUNDS"
    
    return False, "OK"

def detect_traffic_accident_and_transport(cause_deces_text):
    """
    Détecte les mentions d'accidents de circulation dans Cause_deces.
    Cherche les mots-clés "percuté", "renversé", "accident" et identifie le moyen de transport.
    
    Returns:
        (is_traffic_accident: bool, transport_type: str or None)
    """
    if not cause_deces_text or is_missing(cause_deces_text):
        return False, None
    
    text_norm = norm(cause_deces_text)
    
    # Mots-clés d'accident
    accident_keywords = ["percuté", "percute", "renversé", "renverse", "accident"]
    
    # Vérifier si un mot-clé d'accident est présent
    has_accident = any(keyword in text_norm for keyword in accident_keywords)
    
    if not has_accident:
        return False, None
    
    # Liste des moyens de transport à rechercher
    transport_patterns = [
        ("train", ["train", "tgv", "locomotive", "ferroviaire"]),
        ("voiture", ["voiture", "auto", "automobile", "vehicule", "véhicule"]),
        ("camion", ["camion", "poids lourd", "poid lourd", "semi-remorque", "semi remorque"]),
        ("bus", ["bus", "autobus", "autocar", "car"]),
        ("moto", ["moto", "motocyclette", "scooter"]),
        ("vélo", ["velo", "vélo", "bicyclette", "cycliste"]),
        ("tramway", ["tramway", "tram"]),
        ("bateau", ["bateau", "navire", "embarcation", "ferry"]),
        ("avion", ["avion", "aéronef", "aeronef"]),
    ]
    
    # Chercher quel transport est mentionné
    for transport_name, keywords in transport_patterns:
        for keyword in keywords:
            if keyword in text_norm:
                return True, transport_name
    
    # Accident détecté mais transport non identifié
    return True, None

def ensure_country_node(g, country_code_or_name):
    """
    Try to find a country resource in graph by label or prefLabel or ISO code.
    Returns the country URIRef or None.
    """
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    cc = None

    cc = country_from_polish_name(val)

    sval = re.sub(r'[^A-Za-z0-9]', '', val).upper()
    try:
        if cc is None and re.fullmatch(r'[A-Z]{2}', sval):
            c = pycountry.countries.get(alpha_2=sval)
            if c:
                cc = c
        elif cc is None and re.fullmatch(r'[A-Z]{3}', sval):
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
        uri = DATA["alpes_Country_" + iso3.upper()]
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

    slug = re.sub(r'[^a-z0-9_]', '_', norm(country_code_or_name))
    if slug in ("", "nan", "none", "n_a"):
        return None
    uri = DATA["alpes_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(country_code_or_name)))
    return uri


def normalize_age_value(age_value):
    """
    Normalize age values from the Poland dataset.
    Returns tuple: (age_num, age_text, interval_label).
    """
    if age_value is None:
        return None, None, None

    raw = str(age_value).strip()
    if raw == "":
        return None, None, None

    raw_norm = norm(raw)

    interval_match = re.search(r"\b(\d{1,3})\s*[-/]\s*(\d{1,3})\b", raw)
    if interval_match:
        start_age = int(interval_match.group(1))
        end_age = int(interval_match.group(2))
        if 0 <= start_age <= 120 and 0 <= end_age <= 120 and start_age <= end_age:
            return None, None, f"{start_age}-{end_age}"

    if raw_norm in ("unknown", "nieznany"):
        return None, "unknown", None

    if raw == "-":
        return None, "Unknown", None

    match = re.search(r"\d+", raw)
    if match:
        return int(match.group(0)), None, None

    if is_missing(raw):
        return None, None, None

    return None, None, None

def create_age_node(g, age_value):
    """Create an Age or AgeInterval/AgeCategory node and return (node, is_interval)."""
    age_num, age_text, interval_label = normalize_age_value(age_value)
    if age_num is None and age_text is None and interval_label is None:
        return None, False

    bn = BNode()
    if interval_label is not None:
        g.add((bn, RDF.type, F.AgeInterval))
        g.add((bn, RDF.type, F.AgeCategory))
        g.add((bn, RDFS.label, Literal(interval_label)))
        return bn, True

    g.add((bn, RDF.type, F.Age))

    if age_num is not None:
        g.add((bn, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    else:
        g.add((bn, F.hasAge, Literal(age_text)))

    return bn, False

def find_thesaurus_term_by_prefLabel_fr(g, label_fr):
    """Search thesaurus for a subject with SKOS:prefLabel equal to label_fr (fr)."""
    if label_fr is None or str(label_fr).strip() == "":
        return None
    for s,p,o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == norm(label_fr):
            return s
    for s,p,o in g.triples((None, RDFS.label, None)):
        if norm(o) == norm(label_fr):
            return s
    return None

# ---------------- Utilitaires du thesaurus ----------------
def load_death_cause_thesaurus(g):
    """
    Load DeathCause thesaurus from loaded graph.
    Returns dict: normalized_french_label -> URI
    """
    cause_map = {}
    try:
        for cause_uri in g.subjects(RDF.type, T.DeathCause):
            for label_obj in g.objects(cause_uri, SKOS.prefLabel):
                if label_obj.language == "fr" or label_obj.language is None:
                    label_norm = norm(str(label_obj))
                    if label_norm:
                        cause_map[label_norm] = cause_uri
                        print(f"  Thesaurus DeathCause: '{label_obj}' -> {cause_uri}")
        print(f"Loaded {len(cause_map)} DeathCause entries from thesaurus")
    except Exception as e:
        print(f"Warning: Could not load DeathCause thesaurus: {e}")
        import traceback
        traceback.print_exc()
    return cause_map

def load_mapping_csv(mapping_path=MAPPING_PATH):
    """
    Load optional CSV mapping: col1=Alpes_value, col2=Thesaurus_prefLabel
    Returns dict: normalized_alpes_value -> normalized_thesaurus_label
    """
    mapping = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping
    try:
        mdf = pd.read_csv(mapping_path, sep=";", dtype=str)
        cols = list(mdf.columns)
        if len(cols) >= 2:
            alpes_col = cols[0]
            thes_col = cols[1]
            for _, r in mdf.iterrows():
                a = norm(r.get(alpes_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
            print(f"Loaded {len(mapping)} Alpes->Thesaurus mappings from CSV")
            print(f"Columns used: '{alpes_col}' -> '{thes_col}'")
        else:
            print(f"Warning: Expected at least 2 columns in {mapping_path}")
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping

def match_death_cause(value, mapping_dict, thesaurus_map):
    """
    Match Cause_deces value to thesaurus URI.
    Returns (uri, label, is_literal) where is_literal=True if fallback to literal.
    """
    if not value or is_missing(value):
        return None, None, False
    
    val_norm = norm(value)

    # 1) Try explicit CSV mapping
    mapped_label = mapping_dict.get(val_norm)
    if mapped_label:
        uri = thesaurus_map.get(mapped_label)
        if uri:
            return uri, mapped_label, False
        else:
            return None, mapped_label, True

    # 2) Direct thesaurus match
    if val_norm in thesaurus_map:
        return thesaurus_map[val_norm], val_norm, False

    # 3) Substring match
    for lbl, uri in thesaurus_map.items():
        if lbl and lbl in val_norm:
            return uri, lbl, False

    # 4) Word overlap (>=2 words)
    val_words = set(re.findall(r"\b\w+\b", val_norm))
    best = (None, None, 0)
    for lbl, uri in thesaurus_map.items():
        lbl_words = set(re.findall(r"\b\w+\b", lbl))
        overlap = len(val_words & lbl_words)
        if overlap > best[2] and overlap >= 2:
            best = (uri, lbl, overlap)
    if best[0]:
        return best[0], best[1], False

    # Repli vers une valeur litterale
    return None, str(value).strip(), True

# ----------------- Chargement des graphes ----------------
# Charger l'ontologie et le thesaurus pour reference (non exportes)
g_ref = Graph()
g_ref.parse(ONTO_PATH, format="turtle")
g_ref.parse(THES_PATH, format="turtle")

# Create separate graph for data export (without ontology/thesaurus)
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

# Charger le thesaurus DeathCause et le mapping
thesaurus_map = load_death_cause_thesaurus(g_ref)
mapping_dict = load_mapping_csv(MAPPING_PATH)

# -------------------- Lecture du CSV --------------------
encodings_to_try = ["utf-8", "utf-8-sig", "cp1252", "latin-1"]
df = None
for _enc in encodings_to_try:
    try:
        df = pd.read_csv(
            CSV_PATH,
            sep=";",
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
    with open(CSV_PATH, "rb") as fh:
        raw = fh.read().decode("utf-8", errors="replace")
    from io import StringIO
    df = pd.read_csv(StringIO(raw), sep=";", engine="python", dtype=str, keep_default_na=False, na_values=["", "NaN", "nan"])

n_rows = len(df)

# Perimetre du jeu Pologne: conserver uniquement les lignes 3..87 du fichier source
# (first 2 lines are headers), i.e. 85 individuals/events.
MAX_INDIVIDUAL_ROWS = 85
if len(df) > MAX_INDIVIDUAL_ROWS:
    df = df.iloc[:MAX_INDIVIDUAL_ROWS].copy()
    n_rows = len(df)

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
EMBARK_EVENT_CLASS = find_by_label(g_ref, "Embark") or F.EmbarkEvent or F.Event
DEATH_CERTIFICATE_CLASS = find_by_label(g_ref, "DeathCertificate") or F.DeathCertificate

PROP_hasName = find_by_label(g_ref, "hasName") or F.hasName
PROP_hasOfficialName = find_by_label(g_ref, "hasOfficialName") or F.hasOfficialName
PROP_otherName = find_by_label(g_ref, "otherName") or F.otherName
PROP_birthPlace = find_by_label(g_ref, "birth place") or F.birthPlace
PROP_composedOf = find_by_label(g_ref, "composedOf") or F.composedOf
PROP_borderOUT = find_by_label(g_ref, "borderOUT") or F.borderOUT
PROP_borderIN = find_by_label(g_ref, "borderIN") or F.borderIN
PROP_hasAgeLink = find_by_label(g_ref, "aged") or F.aged
PROP_hasAgeInterval = find_by_label(g_ref, "has age interval") or F.hasAgeInterval
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after
PROP_person_involved = find_by_label(g_ref, "involves") or F.involves
PROP_transportType = find_by_label(g_ref, "transportType") or F.transportType
PROP_usedIn = find_by_label(g_ref, "usedIn") or F.usedIn
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasWebLink = find_by_label(g_ref, "hasWebLink") or F.hasWebLink
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_certificate = find_by_label(g_ref, "certificate") or F.certificate
PROP_hasIdCertificate = find_by_label(g_ref, "hasIdCertificate") or F.hasIdCertificate
PROP_hasNarrative = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_targetCountry = find_by_label(g_ref, "target country") or F.targetCountry

THES_male = find_thesaurus_term_by_prefLabel_fr(g_ref, "male") or find_thesaurus_term_by_prefLabel_fr(g_ref, "homme") or T.male
THES_female = find_thesaurus_term_by_prefLabel_fr(g_ref, "female") or find_thesaurus_term_by_prefLabel_fr(g_ref, "femme") or T.female
THES_human = find_thesaurus_term_by_prefLabel_fr(g_ref, "human") or find_thesaurus_term_by_prefLabel_fr(g_ref, "humain") or T.human
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation"])

# ------------------- Traitement des lignes ----------------
created_countries = set()
created_death_events = {}
created_transports = {}
created_collective_events = {}

count_person = 0
count_death_events = 0
count_transports = 0
count_embark = 0
count_collective_events = 0
count_repatriation = 0
count_inhumation = 0
count_cause_matched = 0
count_cause_literal = 0
count_sources = 0
count_traffic_accidents = 0
count_transport_identified = 0
count_death_certificates = 0
count_additional_typed_events = 0

for idx, row in df.iterrows():
    person_uri = DATA["alpes_Person_%d" % (idx+1)]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1

    embark_uri = None
    repatriation_event_uri = None
    inhumation_event_uri = None
    collective_event_uri = None

    # NOMS
    val = row.get("Imię i nazwisko w mediach\nName and surname in the media", "")
    if val and not is_missing(val):
        g.add((person_uri, PROP_hasName, Literal(str(val).strip())))

    val = row.get("Prawidłowie imię i nazwisko\nCorrect name (PL transliteration)", "")
    if val and not is_missing(val):
        g.add((person_uri, PROP_hasOfficialName, Literal(str(val).strip())))

    val = row.get("Autre_nom", "")
    if val and not is_missing(val):
        g.add((person_uri, PROP_otherName, Literal(str(val).strip())))

    # AGE
    age_val = (
        row.get("Wiek\nAge", "")
        or row.get("Wiek", "")
        or row.get("Age", "")
    )
    age_node, is_age_interval = create_age_node(g, age_val)
    if age_node:
        g.add((person_uri, PROP_hasAgeInterval if is_age_interval else PROP_hasAgeLink, age_node))

    # SEXE
    sexe = norm(row.get("Płeć biologiczna\nSex", ""))
    if sexe and not is_missing(sexe):
        if sexe in ("h", "m", "homme", "male", "man", "mezczyzna", "mężczyzna"):
            if THES_male is not None:
                g.add((person_uri, F.gender, THES_male))
            else:
                g.add((person_uri, F.gender, Literal("male")))
        elif sexe in ("f", "femme", "female", "woman", "kobieta"):
            if THES_female is not None:
                g.add((person_uri, F.gender, THES_female))
            else:
                g.add((person_uri, F.gender, Literal("female")))

    # LIEU DE NAISSANCE
    birth_country = None
    if not is_missing(row.get("Kraj pochodzenia\nCountry of origin", "")):
        birth_country = ensure_country_node(g, row.get("Kraj pochodzenia\nCountry of origin"))
    elif not is_missing(row.get("Nati", "")):
        birth_country = ensure_country_node(g, row.get("Nati"))
    if birth_country:
        g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES
    comment_cdb = row.get("Commentaire CDB", "") or row.get("Commentaire_CDB", "")
    if comment_cdb and not is_missing(comment_cdb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))
    
    comment_sb = row.get("Commentaire SB", "") or row.get("Commentaire_SB", "")
    if comment_sb and not is_missing(comment_sb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_sb).strip())))
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Story (on Grupa Granica website)", "Okoliczności\nCircumstances", "Okoliczności", "Circumstances", "Cause_deces"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Comm_enterrement", "Enterrement", "Lokalizacja\nLocation", "Location"], is_missing))

    # EVENEMENT DE DECES
    # Un evenement de deces par ligne CSV; URI indexee sur la ligne pour la reproductibilite.
    event_uri = DATA["alpes_Death_%d" % (idx+1)]

    if str(event_uri) not in created_death_events:
        g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        created_death_events[str(event_uri)] = event_uri
        count_death_events += 1

    g.add((person_uri, PROP_composedOf, event_uri))

    # RÉCIT (Story) lié directement à l'IndividualEvent de décès
    recit_story_val = get_first_non_missing_row_value(
        row,
        exact_names=[
            "Story (on Grupa Granica website)",
            "Okoliczności\nCircumstances",
            "Okoliczności",
            "Circumstances",
            "Okoliczno?ci\nCircumstances",
        ],
        header_keywords=["circumstances", "okolicz"],
    )
    if recit_story_val and not is_missing(recit_story_val):
        g.add((event_uri, PROP_hasNarrative, Literal(str(recit_story_val).strip())))

    # DATE DE DÉCÈS
    # Conserver le format source (ex. DD.MM.YY, D.MM.YY, DD-DD.MM.YY), remplacer seulement '.' par '/'.
    date_mort_val = row.get("Data znalezienia ciała/ śmierci/ informacji\nDate of finding the body/ death/ information", "") or row.get("date_mort", "")
    if date_mort_val and not is_missing(date_mort_val):
        date_str = str(date_mort_val).strip()
        date_str = re.sub(r"\s+", " ", date_str)
        date_out = date_str.replace(".", "/")
        if date_out:
            g.add((event_uri, TIME.inXSDDate, Literal(date_out)))
            weekday_name = infer_day_of_week_name(date_out)
            if weekday_name:
                g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))

    # CAUSE DE DÉCÈS (nouveau mapping avec thésaurus)
    cause_deces_val = row.get("Cause_deces", "") or row.get("cause_deces", "")
    if cause_deces_val and not is_missing(cause_deces_val):
        uri, lbl, is_literal = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        if uri:
            # Triple: Death hasDeathCause URI du thesaurus
            g.add((event_uri, PROP_hasDeathCause, uri))
            count_cause_matched += 1
        elif lbl:
            # Repli: valeur litterale
            g.add((event_uri, PROP_hasDeathCause, Literal(lbl)))
            count_cause_literal += 1
        
        # Détection d'accidents de circulation
        is_accident, transport_type = detect_traffic_accident_and_transport(cause_deces_val)
        if is_accident:
            count_traffic_accidents += 1
            if transport_type:
                count_transport_identified += 1
    
    # CERTIFICAT DE DÉCÈS
    acte_deces_val = row.get("Acte_deces", "") or row.get("acte_deces", "")
    if acte_deces_val and not is_missing(acte_deces_val):
        certificate_uri = DATA["DeathCertificate_%d" % (idx+1)]
        g.add((certificate_uri, RDF.type, DEATH_CERTIFICATE_CLASS))
        g.add((event_uri, PROP_certificate, certificate_uri))
        g.add((certificate_uri, PROP_hasIdCertificate, Literal(str(acte_deces_val).strip())))
        count_death_certificates += 1

    # frontiere_EX -> borderOUT
    front_ex = row.get("Frontiere_EX", "") or row.get("frontiere_EX", "") or row.get("frontiere_EX".lower(), "")
    if not is_missing(front_ex):
        cnode = ensure_country_node(g, str(front_ex).strip())
        if cnode:
            g.add((event_uri, PROP_borderOUT, cnode))

    # frontiere_IN -> borderIN
    front_in = row.get("Frontiere_IN", "") or row.get("frontiere_IN", "") or row.get("frontiere_IN".lower(), "")
    if not is_missing(front_in):
        cnode = ensure_country_node(g, str(front_in).strip())
        if cnode:
            g.add((event_uri, PROP_borderIN, cnode))

    # GEO
    lat = row.get("Coord_Lat_deces", "") or row.get("Coord_lat_deces", "")
    lon = row.get("Coord_Long_deces", "") or row.get("Coord_long_deces", "")
    location_death = (
        row.get("Lokalizacja\nLocation", "")
        or row.get("Lokalizacja", "")
        or row.get("Location", "")
    )
    geometry_added = False
    lat_f = None
    lon_f = None

    try:
        if not is_missing(lat) and not is_missing(lon):
            lat_f = float(lat)
            lon_f = float(lon)
            if math.isfinite(lat_f) and math.isfinite(lon_f):
                # Vérifier si les coordonnées sont suspectes
                is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
                if is_suspicious:
                    print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon_f}, {lat_f}")
                    lat_f = None
                    lon_f = None
    except Exception:
        lat_f = None
        lon_f = None

    # Si les coordonnees explicites sont absentes/invalides, geocoder le texte du lieu de deces.
    if (lat_f is None or lon_f is None) and not is_missing(location_death):
        lat_geo, lon_geo = geocode_event_location(location_death)
        if lat_geo is not None and lon_geo is not None:
            lat_f = lat_geo
            lon_f = lon_geo

    if lat_f is not None and lon_f is not None:
        is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
        if is_suspicious:
            print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon_f}, {lat_f}")
        else:
            wkt = f"POINT({lon_f} {lat_f})"
            geometry_uri = DATA[f"alpes_geometry_{idx+1}"]
            g.add((event_uri, GEO.hasGeometry, geometry_uri))
            g.add((geometry_uri, RDF.type, GEO.Geometry))
            g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
            geometry_added = True

    pays_mort = row.get("Pays_mort", "") or row.get("pays_mort", "") or row.get("Pays_mort".lower(), "")
    if (not geometry_added) and not is_missing(pays_mort):
        country_node = ensure_country_node(g, str(pays_mort).strip())
        if country_node:
            g.add((event_uri, F.paysMort, country_node))

    # TRANSPORT
    transport_val = row.get("transport", "") or row.get("Transport", "") or row.get("transport".lower(), "")
    if not is_missing(transport_val):
        t_norm = norm(transport_val)
        # Transports humains (pas d'événement d'embarquement)
        is_human_transport = any(keyword in t_norm for keyword in ["marche", "nage", "pied", "humain"])
        
        if is_human_transport:
            if THES_human is not None:
                g.add((event_uri, F.transportMode, THES_human))
        else:
            th_term = find_thesaurus_term_by_prefLabel_fr(g_ref, transport_val)
            if th_term is None:
                for s,p,o in g_ref.triples((None, SKOS.prefLabel, None)):
                    if norm(o).find(norm(transport_val)) >= 0:
                        th_term = s
                        break
                if th_term is None:
                    for s,p,o in g_ref.triples((None, RDFS.label, None)):
                        if norm(o).find(norm(transport_val)) >= 0:
                            th_term = s
                            break
            if th_term is not None:
                slug = re.sub(r'[^a-z0-9_]', '_', norm(transport_val))
                if slug and slug not in ("nan", "none", ""):
                    transport_uri = DATA["alpes_Transport_" + slug + "_" + str(idx+1)]
                    if str(transport_uri) not in created_transports:
                        g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
                        g.add((transport_uri, RDF.type, th_term))
                        created_transports[str(transport_uri)] = transport_uri
                        count_transports += 1
                    g.add((event_uri, PROP_transportType, transport_uri))

                    # Créer un événement d'embarquement uniquement pour les transports non-humains
                    embark_uri = DATA["EmbarkEvent_%d_%s" % (idx+1, slug)]
                    if (embark_uri, None, None) not in g:
                        g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                    g.add((embark_uri, PROP_usedIn, transport_uri))
                    g.add((embark_uri, PROP_temporal_before, event_uri))
                    g.add((event_uri, PROP_temporal_after, embark_uri))
                    g.add((person_uri, PROP_composedOf, embark_uri))
                    count_embark += 1

    # COLLECTIVE EVENTS (ID_c)
    id_c = str(row.get("ID_c", "")).strip()
    if id_c and not is_missing(id_c):
        collective_event_uri = DATA["CollectiveEvent_" + re.sub(r'[^A-Za-z0-9_-]', '_', id_c)]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1
            
            # Ajouter le récit si disponible
            recit_val = row.get("Recit_passage_deces", "") or row.get("recit_passage_deces", "")
            if recit_val and not is_missing(recit_val):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(recit_val).strip())))

        # Utiliser uniquement group/memberOf (pas composedOf)
        g.add((event_uri, F.group, collective_event_uri))
        if embark_uri is not None:
            g.add((embark_uri, F.group, collective_event_uri))

    # RAPATRIEMENT
    enterrement_text = str(row.get("Enterrement", "")).strip()
    if ("rapatrié" in norm(enterrement_text) or "rapatriement" in norm(enterrement_text)) and "?" not in enterrement_text:
        repatriation_event_uri = DATA["alpes_Repatriation_%d" % (idx+1)]
        g.add((repatriation_event_uri, RDF.type, F.Repatriation))
        g.add((person_uri, PROP_composedOf, repatriation_event_uri))
        g.add((event_uri, TEMP.before, repatriation_event_uri))
        g.add((repatriation_event_uri, PROP_temporal_after, event_uri))
        if birth_country:
            g.add((repatriation_event_uri, PROP_targetCountry, birth_country))
        count_repatriation += 1

    # INHUMATION
    comm_enterrement = row.get("Comm_enterrement", "")
    if comm_enterrement and not is_missing(comm_enterrement):
        inhumation_event_uri = DATA["InhumationEvent_%d" % (idx+1)]
        if (inhumation_event_uri, None, None) not in g:
            g.add((inhumation_event_uri, RDF.type, F.Inhumation))
        
        g.add((person_uri, PROP_composedOf, inhumation_event_uri))
            
        # Récupérer les coordonnées existantes
        lat_ent = row.get("Coord_Lat_enterrement", "") or row.get("Coord_lat_enterrement", "")
        lon_ent = row.get("Coord_Long_enterrement", "") or row.get("Coord_long_enterrement", "")
        
        lat_e = None
        lon_e = None
        
        # Essayer d'utiliser les coordonnées existantes
        try:
            if not is_missing(lat_ent) and not is_missing(lon_ent):
                lat_e = float(lat_ent)
                lon_e = float(lon_ent)
                if not (math.isfinite(lat_e) and math.isfinite(lon_e)):
                    lat_e = None
                    lon_e = None
        except Exception:
            lat_e = None
            lon_e = None
        
        # Si pas de coordonnées, géocoder Comm_enterrement
        if lat_e is None or lon_e is None:
            lat_e, lon_e = geocode_location(str(comm_enterrement).strip())
            if lat_e is not None and lon_e is not None:
                print(f"Géocodé '{comm_enterrement}' -> ({lat_e}, {lon_e})")
        
        # Ajouter la géométrie si coordonnées disponibles
        if lat_e is not None and lon_e is not None:
            # Vérifier si les coordonnées sont suspectes
            is_suspicious, reason = is_suspicious_coordinate(lat_e, lon_e)
            if is_suspicious:
                print(f"  ⚠️  Coordonnée suspecte ignorée pour inhumation ({reason}): {lon_e}, {lat_e}")
            else:
                wkt_ent = f"POINT({lon_e} {lat_e})"
                geometry_inhumation_uri = DATA[f"pologne_geometry_inhumation_{idx+1}"]
                g.add((inhumation_event_uri, GEO.hasGeometry, geometry_inhumation_uri))
                g.add((geometry_inhumation_uri, RDF.type, GEO.Geometry))
                g.add((geometry_inhumation_uri, GEO.asWKT, Literal(wkt_ent, datatype=GEO.wktLiteral)))
        
        g.add((event_uri, TEMP.before, inhumation_event_uri))
        count_inhumation += 1
        g.add((inhumation_event_uri, PROP_temporal_after, event_uri))
        
        # Optionnel: garder aussi le récit sur l'événement collectif s'il existe
        recit_val = get_first_non_missing_row_value(
            row,
            exact_names=[
                "Story (on Grupa Granica website)",
                "Okoliczności\nCircumstances",
                "Okoliczności",
                "Circumstances",
                "Okoliczno?ci\nCircumstances",
            ],
            header_keywords=["circumstances", "okolicz"],
        )
        if recit_val and not is_missing(recit_val) and collective_event_uri is not None:
            g.add((collective_event_uri, PROP_hasNarrative, Literal(str(recit_val).strip())))
            
    # SOURCE
    source_val = get_first_non_missing_row_value(
        row,
        exact_names=["Źródła\nSources", "Sources", "?r�d?a\nSources"],
        header_keywords=["sources", "source", "zrod", "źród"],
    )
    if source_val and not is_missing(source_val):
        source_str = str(source_val).strip()
        # Vérifier que l'URL commence bien par http
        if source_str.lower().startswith('http'):
            source_uri = DATA["pologne_Source_%d" % (idx+1)]
            g.add((source_uri, RDF.type, F.Source))
            source_category = infer_source_category_key(source_str)
            SOURCE_SUBTYPE_MAP = {"family": F.Family, "media": F.Media, "civil_society": F.CivilSociety, "death_certificate": F.DeathCertificate, "official_document": F.OtherOfficialDocument}
            sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
            if sub_type:
                g.add((source_uri, RDF.type, sub_type))
            g.add((source_uri, PROP_hasWebLink, Literal(source_str)))
            g.add((event_uri, PROP_sourcedBy, source_uri))
            count_sources += 1

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, event_uri)],
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "pologne",
        idx + 1,
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
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "="*60)
print("Import Alpes complete.")
print("="*60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created: {count_death_events}")
print(f"Transport individuals created: {count_transports}")
print(f"Embark events created: {count_embark}")
print(f"Collective events created: {count_collective_events}")
print(f"Repatriation events created: {count_repatriation}")
print(f"Inhumation events created: {count_inhumation}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Sources created: {count_sources}")
print(f"Death certificates created: {count_death_certificates}")
print(f"\nCause de décès - mapping avec thésaurus:")
print(f"  - Matched to thesaurus URI: {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"\nDétection d'accidents de circulation:")
print(f"  - Accidents détectés (percuté/renversé/accident): {count_traffic_accidents}")
print(f"  - Moyen de transport identifié: {count_transport_identified}")
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

