#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV Italie_CPR -> ontologie RDF selon vos regles.
Amelioration du mapping Cause_deces avec le thesaurus DeathCause (prefLabel@fr)
"""

from rdflib import Graph, Namespace, URIRef, BNode, Literal
from rdflib.namespace import RDF, RDFS, SKOS, XSD
import pandas as pd
import unicodedata
import re
import os
import math
import json
import pycountry
from datetime import datetime
from geopy.geocoders import Nominatim
from geopy.exc import GeocoderTimedOut, GeocoderServiceError
import time
from event_text_utils import (
    add_additional_typed_events,
    add_event_country_from_geometry,
    build_additional_event_specs,
    build_cemetery_geocode_cache,
    build_wkt_for_location_precision,
    collect_text_values_from_row,
    infer_day_of_week_name,
    infer_source_category_key,
    propagate_geometry_to_sibling_events,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
CSV_PATH = "Italie_CPR/Italie_CPR.csv"
OUTPUT_TTL = "Italie_CPR/frontlet_import_output.ttl"
MAPPING_PATH = "Italie_CPR/mappingItalieCPRThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)
GEOCODE_CACHE_PATH = "Italie_CPR/geocode_cache.json"
GEOCODE_MIN_DELAY_SECONDS = 1.2
GEOCODE_429_BACKOFF_SECONDS = 8.0
GEOCODE_MAX_429_RETRIES = 2
GEOCODE_MODE = os.environ.get("ITALIE_CPR_GEOCODE_MODE", "live").strip().lower()
ALLOW_LIVE_GEOCODING = GEOCODE_MODE in ("online", "live", "refresh")
REFRESH_CAMP_CACHE = os.environ.get("ITALIE_CPR_REFRESH_CAMP_CACHE", "1").strip().lower() not in ("0", "false", "no")

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
geolocator = Nominatim(user_agent="frontlet_italie_cpr_geocoder")
GEOCODER_RATE_LIMITED = False
LAST_GEOCODE_REQUEST_TS = 0.0


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


def is_coordinate_in_italy_bbox(lat, lon):
    """Quick geographic guardrail to keep CPR/CIE/CPT geocodes in Italy."""
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return False
    return 35.0 <= lat_f <= 48.5 and 6.0 <= lon_f <= 19.5


def sanitize_location_text(text):
    cleaned = str(text).strip()
    cleaned = cleaned.replace("’", "'")
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned.strip(" ,;.-")


def build_location_candidates(location_str):
    """Build a list of increasingly relaxed location queries from any free-text chain."""
    base = sanitize_location_text(location_str)
    if base == "":
        return []

    candidates = [base]

    # Remove detention-center acronyms and common stop words while keeping place tokens.
    no_center = re.sub(r"\b(cpt|cie|cpr|cpa|centro|center|detenzione|detention)\b", " ", base, flags=re.IGNORECASE)
    no_center = re.sub(r"\b(di|del|della|dell|dei|degli|delle|de|du|des)\b", " ", no_center, flags=re.IGNORECASE)
    no_center = re.sub(r"\s+", " ", no_center).strip(" ,;.-")
    if no_center:
        candidates.append(no_center)

    # Decouper les chaines comme "Cpr Restinco, Brindisi" et conserver chaque segment.
    parts = [p.strip(" ,;.-") for p in re.split(r"[,;/|]", base) if p.strip(" ,;.-")]
    candidates.extend(parts)

    # Right-most segment often contains the city.
    if parts:
        candidates.append(parts[-1])

    # Also try with dashes removed in case of composed labels.
    dash_simplified = re.sub(r"\s*-\s*", " ", no_center or base)
    dash_simplified = re.sub(r"\s+", " ", dash_simplified).strip(" ,;.-")
    if dash_simplified:
        candidates.append(dash_simplified)

    # Add country-context variants to force Italian matching.
    with_country = []
    for c in candidates:
        with_country.append(c)
        with_country.append(f"{c}, Italy")
        with_country.append(f"{c}, Italia")

    seen = set()
    deduped = []
    for c in with_country:
        key = norm(c)
        if key and key not in seen:
            seen.add(key)
            deduped.append(c)
    return deduped


def is_camp_like_location(location_text):
    txt = norm(location_text)
    return bool(re.search(r"\b(cpt|cie|cpr|centro|detenzione|detention|hotspot)\b", txt))


def select_best_camp_result(results, candidate):
    """Select the best camp-like result deterministically from a geocoder result list."""
    if not results:
        return None

    camp_tokens = (
        "cpr", "cie", "cpt", "detention", "detenzione", "migrant", "immigration", "hotspot", "accoglienza",
    )
    cand_norm = norm(candidate)
    ranked = []

    for loc in results:
        addr = norm(getattr(loc, "address", ""))
        if not addr:
            continue
        score = 0
        for token in camp_tokens:
            if token in addr:
                score += 1
        if cand_norm and cand_norm in addr:
            score += 2
        ranked.append((score, addr, loc))

    if not ranked:
        return None

    ranked.sort(key=lambda x: (-x[0], x[1]))
    return ranked[0][2]


def geocode_location(location_name, geocode_cache, max_retries=3):
    """
    Geocode un nom de lieu et retourne (latitude, longitude) ou (None, None).
    Cherche d'abord un cimetiere, sinon utilise le centroide de la ville.
    """
    if is_missing(location_name):
        return None, None

    location_str = str(location_name).strip()
    camp_like = is_camp_like_location(location_str)

    cache_key = norm(location_str)
    cached = geocode_cache.get(cache_key)
    cached_coords = None
    if isinstance(cached, dict) and "lat" in cached and "lon" in cached:
        try:
            cached_query = norm(cached.get("query", ""))
            cached_provider = norm(cached.get("provider", ""))
            if cached_query == "known_italy_camp_registry" or cached_provider == "registry":
                # Drop legacy fixed-point cache entries so coordinates can refresh from live geocoding.
                geocode_cache.pop(cache_key, None)
                cached = None
            else:
                cached_coords = (float(cached["lat"]), float(cached["lon"]))
                if not is_coordinate_in_italy_bbox(cached_coords[0], cached_coords[1]):
                    geocode_cache.pop(cache_key, None)
                    cached_coords = None
                if not (camp_like and REFRESH_CAMP_CACHE and ALLOW_LIVE_GEOCODING):
                    return cached_coords
        except Exception:
            cached_coords = None

    # Optional deterministic mode for strict reproducibility.
    if not ALLOW_LIVE_GEOCODING:
        return None, None

    candidates = build_location_candidates(location_str)
    if not candidates:
        return cached_coords if cached_coords is not None else (None, None)

    for candidate in candidates:
        for attempt in range(max_retries):
            try:
                if camp_like:
                    camp_queries = [
                        f"cpr {candidate}",
                        f"cie {candidate}",
                        f"cpt {candidate}",
                        f"detention center {candidate}",
                        f"immigration detention {candidate}",
                        f"centro di permanenza per il rimpatrio {candidate}",
                    ]

                    for camp_query in camp_queries:
                        throttle_geocode_requests()
                        camp_results = geolocator.geocode(
                            camp_query,
                            exactly_one=False,
                            limit=6,
                            timeout=10,
                            country_codes="it",
                        )
                        best_camp = select_best_camp_result(camp_results, candidate)
                        if best_camp is not None:
                            lat = float(best_camp.latitude)
                            lon = float(best_camp.longitude)
                            if not is_coordinate_in_italy_bbox(lat, lon):
                                continue
                            geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": camp_query}
                            return lat, lon

                cemetery_query = f"cemetery {candidate}"
                throttle_geocode_requests()
                results = geolocator.geocode(
                    cemetery_query,
                    exactly_one=False,
                    limit=5,
                    timeout=10,
                    country_codes="it",
                )

                if results:
                    cemetery_results = [
                        r for r in results
                        if "cemetery" in r.address.lower() or "cimetiere" in r.address.lower() or "cementerio" in r.address.lower()
                    ]
                    if len(cemetery_results) == 1:
                        lat = float(cemetery_results[0].latitude)
                        lon = float(cemetery_results[0].longitude)
                        if not is_coordinate_in_italy_bbox(lat, lon):
                            break
                        geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": candidate}
                        return lat, lon

                throttle_geocode_requests()
                location = geolocator.geocode(candidate, timeout=10, country_codes="it")
                if location:
                    lat = float(location.latitude)
                    lon = float(location.longitude)
                    if not is_coordinate_in_italy_bbox(lat, lon):
                        break
                    geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": candidate}
                    return lat, lon

                break

            except GeocoderTimedOut:
                if attempt < max_retries - 1:
                    time.sleep(1)
                    continue
                break
            except GeocoderServiceError as e:
                if is_http_429_error(e):
                    for retry_429 in range(GEOCODE_MAX_429_RETRIES):
                        time.sleep(GEOCODE_429_BACKOFF_SECONDS * (retry_429 + 1))
                        try:
                            throttle_geocode_requests()
                            location = geolocator.geocode(candidate, timeout=10, country_codes="it")
                            if location:
                                lat = float(location.latitude)
                                lon = float(location.longitude)
                                if not is_coordinate_in_italy_bbox(lat, lon):
                                    continue
                                geocode_cache[cache_key] = {"lat": lat, "lon": lon, "query": candidate}
                                return lat, lon
                        except Exception:
                            pass
                    return None, None
                break
            except Exception as e:
                if is_http_429_error(e):
                    return None, None
                break

    if cached_coords is not None:
        return cached_coords
    return None, None


def is_suspicious_coordinate(lat, lon):
    """
    Verifie si les coordonnees sont suspectes et doivent etre ignorees.
    Retourne (is_suspicious: bool, reason: str)
    """
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


def detect_traffic_accident_and_transport(cause_deces_text):
    """
    Detecte les mentions d'accidents de circulation dans Cause_deces.
    """
    if not cause_deces_text or is_missing(cause_deces_text):
        return False, None

    text_norm = norm(cause_deces_text)
    accident_keywords = ["percute", "renverse", "accident"]
    has_accident = any(keyword in text_norm for keyword in accident_keywords)

    if not has_accident:
        return False, None

    transport_patterns = [
        ("train", ["train", "tgv", "locomotive", "ferroviaire"]),
        ("voiture", ["voiture", "auto", "automobile", "vehicule", "vehicule"]),
        ("camion", ["camion", "poids lourd", "poid lourd", "semi-remorque", "semi remorque"]),
        ("bus", ["bus", "autobus", "autocar", "car"]),
        ("moto", ["moto", "motocyclette", "scooter"]),
        ("velo", ["velo", "bicyclette", "cycliste"]),
        ("tramway", ["tramway", "tram"]),
        ("bateau", ["bateau", "navire", "embarcation", "ferry"]),
        ("avion", ["avion", "aeronef"]),
    ]

    for transport_name, keywords in transport_patterns:
        for keyword in keywords:
            if keyword in text_norm:
                return True, transport_name

    return True, None


def detect_transport_from_text(*values):
    """Detect transport mode from one or more text fragments (it/fr/en)."""
    text = " ".join(str(v) for v in values if v is not None and not is_missing(v))
    txt = norm(text)
    if txt == "":
        return None

    def _contains_term(haystack, term):
        # Match term as full token(s) to avoid substring false positives
        # such as "car" in "cardiaca" or "bus" in "busto".
        parts = [re.escape(p) for p in term.split() if p]
        if not parts:
            return False
        pattern = r"\\b" + r"\\s+".join(parts) + r"\\b"
        return re.search(pattern, haystack) is not None

    transport_patterns = [
        ("small boat", ["barca", "barche", "barcone", "imbarcazione", "bateau", "boat", "ship", "ferry", "gommone"]),
        ("train", ["train", "treno", "rail", "ferrovia"]),
        ("truck", ["truck", "camion", "lorry", "tir", "semi-remorque"]),
        ("bus", ["bus", "autobus", "autocar", "coach"]),
        ("car", ["voiture", "auto", "automobile", "vehicule", "vehicle"]),
        ("plane", ["plane", "avion", "aereo", "aircraft"]),
        ("motorbike", ["moto", "motocyclette", "motorbike", "motorcycle", "scooter"]),
        ("bicycle", ["velo", "bicycle", "bike", "cycliste"]),
    ]

    for token, keywords in transport_patterns:
        if any(_contains_term(txt, k) for k in keywords):
            return token
    return None


ITALIAN_COUNTRY_NAMES = {
    # Noms italiens → noms anglais reconnus par pycountry
    "marocco": "Morocco",
    "brasile": "Brazil",
    "egitto": "Egypt",
    "libia": "Libya",
    "siria": "Syria",
    "giordania": "Jordan",
    "turchia": "Turkey",
    "grecia": "Greece",
    "spagna": "Spain",
    "francia": "France",
    "germania": "Germany",
    "gran bretagna": "United Kingdom",
    "regno unito": "United Kingdom",
    "paesi bassi": "Netherlands",
    "olanda": "Netherlands",
    "svizzera": "Switzerland",
    "cina": "China",
    "giappone": "Japan",
    "corea del sud": "South Korea",
    "corea del nord": "North Korea",
    "costa d'avorio": "Ivory Coast",
    "costa davorio": "Ivory Coast",
    "etiopia": "Ethiopia",
    "ucraina": "Ukraine",
    # Formes adjectivales → nom du pays
    "nigeriano": "Nigeria",
    "albanese": "Albania",
    "marocchino": "Morocco",
    "tunisino": "Tunisia",
    "algerino": "Algeria",
    "egiziano": "Egypt",
    "eritreo": "Eritrea",
    "senegalese": "Senegal",
    "gambiano": "Gambia",
    "ghanese": "Ghana",
}

def _resolve_italian_country_name(val):
    """Normalise un nom de pays en supprimant les astérisques et en tentant la table italienne."""
    cleaned = re.sub(r"[*\s]+$", "", val).strip()  # retire * et espaces en fin
    key = cleaned.lower()
    if key in ITALIAN_COUNTRY_NAMES:
        return ITALIAN_COUNTRY_NAMES[key]
    # Essai sans accents (au cas où)
    key_norm = unicodedata.normalize("NFD", key)
    key_norm = "".join(c for c in key_norm if unicodedata.category(c) != "Mn")
    if key_norm in ITALIAN_COUNTRY_NAMES:
        return ITALIAN_COUNTRY_NAMES[key_norm]
    return cleaned


def ensure_country_node(g, country_code_or_name):
    """
    Try to find a country resource in graph by label or prefLabel or ISO code.
    Returns the country URIRef or None.
    """
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    # Résolution des noms italiens / formes adjectivales avant recherche fuzzy
    resolved_name = _resolve_italian_country_name(val)
    if resolved_name != val:
        val = resolved_name

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
        uri = DATA["italie_Country_" + iso3.upper()]
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
    uri = DATA["italie_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(country_code_or_name)))
    return uri


def create_age_node(g, age_value, age_uri=None):
    """Create an Age node and return it."""
    if age_value is None or is_missing(age_value):
        return None
    try:
        age_num = int(float(str(age_value).strip()))
    except Exception:
        return None
    age_node = age_uri if age_uri is not None else BNode()
    g.add((age_node, RDF.type, F.Age))
    g.add((age_node, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    return age_node


def find_thesaurus_term_by_prefLabel_fr(g, label_fr):
    """Search thesaurus for a subject with SKOS:prefLabel equal to label_fr (fr)."""
    if label_fr is None or str(label_fr).strip() == "":
        return None
    for s, p, o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == norm(label_fr):
            return s
    for s, p, o in g.triples((None, RDFS.label, None)):
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
        print(f"Loaded {len(cause_map)} DeathCause entries from thesaurus")
    except Exception as e:
        print(f"Warning: Could not load DeathCause thesaurus: {e}")
    return cause_map


def load_mapping_csv(mapping_path=MAPPING_PATH):
    """
    Load optional CSV mapping: col1=source_value, col2=Thesaurus_prefLabel
    Returns (mapping_dict, mapping_nature)
    """
    mapping = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping, mapping_nature
    try:
        for _enc in ("utf-8", "latin-1", "cp1252"):
            try:
                mdf = pd.read_csv(mapping_path, sep=";", dtype=str, encoding=_enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            raise UnicodeDecodeError("utf-8", b"", 0, 1, "Could not decode with any tried encoding")
        cols = list(mdf.columns)
        if len(cols) >= 2:
            src_col = cols[0]
            thes_col = cols[1]
            nature_col = cols[2] if len(cols) >= 3 and "nature" in str(cols[2]).lower() else None
            for _, r in mdf.iterrows():
                a = norm(r.get(src_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
                if nature_col:
                    n = str(r.get(nature_col, "")).strip()
                    if a and n and n.lower() not in ("", "nan", "none"):
                        mapping_nature[a] = n
            print(f"Loaded {len(mapping)} source->Thesaurus mappings and {len(mapping_nature)} Nature mappings from CSV")
        else:
            print(f"Warning: Expected at least 2 columns in {mapping_path}")
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping, mapping_nature


def match_death_cause(value, mapping_dict, thesaurus_map):
    """
    Match cause value to thesaurus URI.
    Returns (uri, label, is_literal) where is_literal=True if fallback to literal.
    """
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


def create_or_get_death_cause_instance(graph, label_text, match_uri=None):
    """Create/reuse a frontlet:DeathCause individual from a label."""
    if is_missing(label_text):
        return None
    slug = re.sub(r"[^a-z0-9_]", "_", norm(label_text)).strip("_")
    if slug == "":
        return None
    uri = DATA[f"italie_cpr_DeathCause_{slug}"]
    if (uri, RDF.type, F.DeathCause) not in graph:
        graph.add((uri, RDF.type, F.DeathCause))
        graph.add((uri, RDFS.label, Literal(str(label_text).strip())))
        if match_uri is not None:
            graph.add((uri, SKOS.closeMatch, match_uri))
    return uri


def create_or_get_death_nature_instance(graph, label_text):
    """Create/reuse a frontlet:DeathNature individual from a label."""
    if is_missing(label_text):
        return None
    slug = re.sub(r"[^a-z0-9_]", "_", norm(label_text)).strip("_")
    if slug == "":
        return None
    uri = DATA[f"italie_cpr_DeathNature_{slug}"]
    if (uri, RDF.type, F.DeathNature) not in graph:
        graph.add((uri, RDF.type, F.DeathNature))
        graph.add((uri, RDFS.label, Literal(str(label_text).strip())))
    return uri


def estimate_missing_injury_counts(*values):
    """Estimate missing/injury counts from free text, with numeric preference."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return 0, 0

    def _find_count(pattern):
        m = re.search(pattern, txt)
        if not m:
            return 0
        try:
            return max(0, int(m.group(1)))
        except Exception:
            return 0

    missing_count = _find_count(r"\b(\d{1,3})\s+(?:missing|dispers[oi]|scompars[oi])\b")
    injury_count = _find_count(r"\b(\d{1,3})\s+(?:injured|wounded|ferit[oi]|bless[ée]s?)\b")

    if missing_count == 0 and any(k in txt for k in ["missing", "dispers", "scompar"]):
        missing_count = 1
    if injury_count == 0 and any(k in txt for k in ["injured", "wounded", "ferit", "bless"]):
        injury_count = 1

    return missing_count, injury_count


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


# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or F.Injury
MISSING_EVENT_CLASS = F.Missing
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
PROP_hasAgeLiteral = find_by_label(g_ref, "hasAge") or F.hasAge
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after
PROP_transportType = find_by_label(g_ref, "transportType") or F.transportType
PROP_usedIn = find_by_label(g_ref, "usedIn") or F.usedIn
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasWebLink = find_by_label(g_ref, "hasWebLink") or F.hasWebLink
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_certificate = find_by_label(g_ref, "certificate") or F.certificate
PROP_hasIdCertificate = find_by_label(g_ref, "hasIdCertificate") or F.hasIdCertificate
PROP_hasNarrative = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_targetCountry = find_by_label(g_ref, "target country") or F.targetCountry

THES_human = find_thesaurus_term_by_prefLabel_fr(g_ref, "human") or find_thesaurus_term_by_prefLabel_fr(g_ref, "humain") or T.human
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation"])


# ------------------- Traitement des lignes ----------------
created_death_events = {}
created_transports = {}
created_collective_events = {}

count_person = 0
count_death_events = 0
count_injury_events = 0
count_missing_events = 0
count_transports = 0
count_embark = 0
count_collective_events = 0
count_repatriation = 0
count_inhumation = 0
count_cause_matched = 0
count_cause_literal = 0
count_nature_mapped = 0
count_sources = 0
count_traffic_accidents = 0
count_transport_identified = 0
count_death_certificates = 0
count_geocode_success = 0
count_geocode_failed = 0
count_additional_typed_events = 0

geocode_cache = load_geocode_cache(GEOCODE_CACHE_PATH)

for idx, row in df.iterrows():
    person_uri = DATA["italie_Person_%d" % (idx + 1)]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1
    collective_event_uri = None

    embark_uri = None

    # NOMS (variable demandee: Nome)
    val = row.get("Nome", "")
    if val and not is_missing(val):
        person_name = Literal(str(val).strip())
        name_uri = DATA["italie_Name_%d" % (idx + 1)]
        g.add((name_uri, RDFS.label, person_name))
        # Lien objet explicite pour visualiser le nom comme noeud dans le graphe.
        g.add((person_uri, PROP_hasName, name_uri))
        g.add((person_uri, PROP_hasOfficialName, person_name))
        g.add((person_uri, RDFS.label, person_name))

    # AGE (variable demandee: Età)
    age_node = None
    age_val = row.get("Età", "") or row.get("Eta", "")
    try:
        if age_val is not None and age_val != "" and not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
            age_uri = DATA["italie_Age_%d" % (idx + 1)]
            age_node = create_age_node(g, age_val, age_uri=age_uri)
            if age_node:
                g.add((person_uri, PROP_hasAgeLink, age_node))
                for age_v in g.objects(age_node, F.hasAge):
                    g.add((person_uri, PROP_hasAgeLiteral, age_v))
    except Exception:
        pass

    # LIEU DE NAISSANCE (variable demandee: Paese d'origine)
    birth_country = None
    paese_origine = row.get("Paese d'origine", "") or row.get("Paese d’origine", "")
    if not is_missing(paese_origine):
        birth_country = ensure_country_node(g, paese_origine)
    if birth_country:
        g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES (gardes dans la structure)
    comment_cdb = row.get("Commentaire CDB", "") or row.get("Commentaire_CDB", "")
    if comment_cdb and not is_missing(comment_cdb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))

    comment_sb = row.get("Commentaire SB", "") or row.get("Commentaire_SB", "")
    if comment_sb and not is_missing(comment_sb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_sb).strip())))
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Causa della morta", "Causa della morte", "Recit_passage_deces", "Commentaire CDB", "Commentaire SB"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Comm_enterrement", "Enterrement", "Source", "Struttura"], is_missing))

    # EVENEMENT DE DECES
    # L'URI est liee a l'index de ligne CSV pour rendre les IDs exportes reproductibles.
    event_uri = DATA["italie_Death_%d" % (idx + 1)]

    if str(event_uri) not in created_death_events:
        g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        created_death_events[str(event_uri)] = event_uri
        count_death_events += 1

    g.add((person_uri, PROP_composedOf, event_uri))
    person_event_pairs = [(person_uri, event_uri)]

    # CAUSE DE DECES (utilisee aussi pour certains fallbacks)
    cause_deces_val = row.get("Causa della morta", "") or row.get("Causa della morte", "")

    # DATE DE DECES (variable demandee: Data decesso e evento critico)
    date_mort_val = row.get("Data decesso e evento critico", "") or row.get("Data decesso o evento critico", "")
    if date_mort_val and not is_missing(date_mort_val):
        try:
            date_str = str(date_mort_val).strip()
            parsed_date = None

            # Cas "14-15.10.2007" -> "14.10.2007"
            date_str = re.sub(r"^(\d{1,2})\s*[-/]\s*\d{1,2}(?=[./-]\d{1,2}[./-]\d{4}$)", r"\1", date_str)

            for fmt in ["%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%d.%m.%Y"]:
                try:
                    parsed_date = datetime.strptime(date_str, fmt)
                    break
                except ValueError:
                    pass

            if not parsed_date and re.fullmatch(r"\d{4}", date_str):
                parsed_date = datetime.strptime(date_str + "-01-01", "%Y-%m-%d")

            if not parsed_date:
                year_match = re.search(r"\b(19\d{2}|20\d{2})\b", date_str)
                if year_match:
                    parsed_date = datetime.strptime(year_match.group(1) + "-01-01", "%Y-%m-%d")

            if parsed_date:
                date_iso = parsed_date.strftime("%Y-%m-%d")
                g.add((event_uri, TIME.inXSDDate, Literal(date_iso, datatype=XSD.date)))
                weekday_name = infer_day_of_week_name(date_iso)
                if weekday_name:
                    g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                    g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                    g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
            else:
                weekday_name = infer_day_of_week_name(date_str, cause_deces_val, row.get("Struttura", ""))
                if weekday_name:
                    g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                    g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                    g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
        except Exception as e:
            print(f"Erreur parsing date pour ligne {idx + 1}: {date_mort_val} - {e}")

    # CAUSE DE DECES (variable demandee: Causa della morta)
    if cause_deces_val and not is_missing(cause_deces_val):
        uri, lbl, _ = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        cause_label = lbl if lbl else cause_deces_val
        cause_instance = create_or_get_death_cause_instance(g, cause_label, uri)
        if cause_instance is not None:
            g.add((event_uri, PROP_hasDeathCause, cause_instance))
            count_cause_matched += 1
        elif lbl:
            g.add((event_uri, PROP_hasDeathCause, Literal(lbl)))
            count_cause_literal += 1

        nature_label = mapping_nature.get(norm(cause_deces_val))
        if nature_label:
            nature_instance = create_or_get_death_nature_instance(g, nature_label)
            if nature_instance is not None:
                g.add((event_uri, PROP_hasDeathNature, nature_instance))
                count_nature_mapped += 1

        is_accident, transport_type = detect_traffic_accident_and_transport(cause_deces_val)
        if is_accident:
            count_traffic_accidents += 1
            if transport_type:
                count_transport_identified += 1

    missing_count, injury_count = estimate_missing_injury_counts(
        row.get("Recit_passage_deces", ""),
        row.get("Commentaire CDB", ""),
        row.get("Commentaire SB", ""),
        cause_deces_val,
    )
    for add_idx in range(missing_count):
        miss_uri = DATA[f"italie_MissingEvent_{idx + 1}_{add_idx + 1}"]
        g.add((miss_uri, RDF.type, MISSING_EVENT_CLASS))
        g.add((miss_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, miss_uri))
        g.add((miss_uri, PROP_temporal_before, event_uri))
        g.add((event_uri, PROP_temporal_after, miss_uri))
        if collective_event_uri is not None:
            g.add((miss_uri, F.group, collective_event_uri))
        person_event_pairs.append((person_uri, miss_uri))
        count_missing_events += 1

    for add_idx in range(injury_count):
        injury_uri = DATA[f"italie_InjuryEvent_{idx + 1}_{add_idx + 1}"]
        g.add((injury_uri, RDF.type, INJURY_EVENT_CLASS))
        g.add((injury_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, injury_uri))
        g.add((injury_uri, PROP_temporal_before, event_uri))
        g.add((event_uri, PROP_temporal_after, injury_uri))
        if collective_event_uri is not None:
            g.add((injury_uri, F.group, collective_event_uri))
        person_event_pairs.append((person_uri, injury_uri))
        count_injury_events += 1

    # CERTIFICAT DE DECES (conserve)
    acte_deces_val = row.get("Acte_deces", "") or row.get("acte_deces", "")
    if acte_deces_val and not is_missing(acte_deces_val):
        certificate_uri = DATA["DeathCertificate_%d" % (idx + 1)]
        g.add((certificate_uri, RDF.type, DEATH_CERTIFICATE_CLASS))
        g.add((event_uri, PROP_certificate, certificate_uri))
        g.add((certificate_uri, PROP_hasIdCertificate, Literal(str(acte_deces_val).strip())))
        count_death_certificates += 1

    # GEO (variable demandee: Struttura geocodee -> WKT)
    struttura_val = row.get("Struttura", "")
    if struttura_val and not is_missing(struttura_val):
        lat_f, lon_f = geocode_location(str(struttura_val).strip(), geocode_cache)
        if lat_f is not None and lon_f is not None and math.isfinite(float(lat_f)) and math.isfinite(float(lon_f)):
            is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
            if is_suspicious:
                count_geocode_failed += 1
            else:
                wkt = build_wkt_for_location_precision(struttura_val, float(lat_f), float(lon_f), True)
                geometry_uri = DATA[f"italie_geometry_{idx + 1}"]
                g.add((event_uri, GEO.hasGeometry, geometry_uri))
                g.add((geometry_uri, RDF.type, GEO.Geometry))
                g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
                # Localisation toujours géocodée pour les CPR
                g.add((geometry_uri, F.hasPrecision, Literal(False, datatype=XSD.boolean)))
                if struttura_val and not is_missing(struttura_val):
                    g.add((event_uri, F.lieu, Literal(str(struttura_val).strip())))
                count_geocode_success += 1
        else:
            count_geocode_failed += 1

    # TRANSPORT (structure conservee)
    transport_val = row.get("transport", "") or row.get("Transport", "")
    if is_missing(transport_val):
        transport_val = detect_transport_from_text(
            cause_deces_val,
            row.get("Recit_passage_deces", ""),
            row.get("Commentaire CDB", ""),
            row.get("Commentaire SB", ""),
            row.get("Struttura", ""),
        )
    if not is_missing(transport_val):
        t_norm = norm(transport_val)
        is_human_transport = any(keyword in t_norm for keyword in ["marche", "nage", "pied", "humain"])

        if is_human_transport:
            if THES_human is not None:
                g.add((event_uri, F.transportMode, THES_human))
        else:
            th_term = find_thesaurus_term_by_prefLabel_fr(g_ref, transport_val)
            if th_term is None:
                for s, p, o in g_ref.triples((None, SKOS.prefLabel, None)):
                    if norm(transport_val) in norm(o):
                        th_term = s
                        break
            if th_term is None:
                for s, p, o in g_ref.triples((None, RDFS.label, None)):
                    if norm(transport_val) in norm(o):
                        th_term = s
                        break
            if th_term is not None:
                slug = re.sub(r"[^a-z0-9_]", "_", norm(transport_val))
                if slug and slug not in ("nan", "none", ""):
                    transport_uri = DATA["italie_Transport_" + slug + "_" + str(idx + 1)]
                    if str(transport_uri) not in created_transports:
                        g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
                        g.add((transport_uri, RDF.type, th_term))
                        created_transports[str(transport_uri)] = transport_uri
                        count_transports += 1
                    g.add((event_uri, PROP_transportType, transport_uri))
                    g.add((transport_uri, PROP_usedIn, event_uri))

                    embark_uri = DATA["EmbarkEvent_%d_%s" % (idx + 1, slug)]
                    if (embark_uri, None, None) not in g:
                        g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                    g.add((embark_uri, PROP_usedIn, transport_uri))
                    g.add((embark_uri, PROP_temporal_before, event_uri))
                    g.add((event_uri, PROP_temporal_after, embark_uri))
                    g.add((person_uri, PROP_composedOf, embark_uri))
                    count_embark += 1

    # COLLECTIVE EVENTS (structure conservee)
    id_c = str(row.get("ID_c", "")).strip()
    if id_c and not is_missing(id_c):
        collective_event_uri = DATA["CollectiveEvent_" + re.sub(r"[^A-Za-z0-9_-]", "_", id_c)]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1

            recit_val = row.get("Recit_passage_deces", "") or row.get("recit_passage_deces", "")
            if recit_val and not is_missing(recit_val):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(recit_val).strip())))

        g.add((event_uri, F.group, collective_event_uri))
        if embark_uri is not None:
            g.add((embark_uri, F.group, collective_event_uri))

    # RAPATRIEMENT (structure conservee)
    enterrement_text = str(row.get("Enterrement", "")).strip()
    if ("rapatrie" in norm(enterrement_text) or "rapatriement" in norm(enterrement_text)) and "?" not in enterrement_text:
        repatriation_event_uri = DATA["italie_Repatriation_%d" % (idx + 1)]
        g.add((repatriation_event_uri, RDF.type, F.Repatriation))
        g.add((repatriation_event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, repatriation_event_uri))
        g.add((event_uri, TEMP.before, repatriation_event_uri))
        g.add((repatriation_event_uri, PROP_temporal_after, event_uri))
        if birth_country:
            g.add((repatriation_event_uri, PROP_targetCountry, birth_country))
        count_repatriation += 1

    # INHUMATION (structure conservee)
    comm_enterrement = row.get("Comm_enterrement", "")
    if comm_enterrement and not is_missing(comm_enterrement):
        inhumation_event_uri = DATA["InhumationEvent_%d" % (idx + 1)]
        if (inhumation_event_uri, None, None) not in g:
            g.add((inhumation_event_uri, RDF.type, F.Inhumation))
            g.add((inhumation_event_uri, RDF.type, F.IndividualEvent))

        g.add((person_uri, PROP_composedOf, inhumation_event_uri))

        lat_ent = row.get("Coord_Lat_enterrement", "") or row.get("Coord_lat_enterrement", "")
        lon_ent = row.get("Coord_Long_enterrement", "") or row.get("Coord_long_enterrement", "")

        lat_e = None
        lon_e = None
        inhumation_geocoded_fallback = False

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

        if lat_e is None or lon_e is None:
            lat_e, lon_e = geocode_location(str(comm_enterrement).strip())
            if lat_e is not None and lon_e is not None:
                inhumation_geocoded_fallback = True

        if lat_e is not None and lon_e is not None:
            is_suspicious, reason = is_suspicious_coordinate(lat_e, lon_e)
            if not is_suspicious:
                wkt_ent = build_wkt_for_location_precision(comm_enterrement, lat_e, lon_e, False)
                geometry_inhumation_uri = DATA[f"italie_geometry_inhumation_{idx + 1}"]
                g.add((inhumation_event_uri, GEO.hasGeometry, geometry_inhumation_uri))
                g.add((geometry_inhumation_uri, RDF.type, GEO.Geometry))
                g.add((geometry_inhumation_uri, GEO.asWKT, Literal(wkt_ent, datatype=GEO.wktLiteral)))
                g.add((geometry_inhumation_uri, F.hasPrecision, Literal(not inhumation_geocoded_fallback, datatype=XSD.boolean)))
                if inhumation_geocoded_fallback and comm_enterrement and not is_missing(comm_enterrement):
                    g.add((inhumation_event_uri, F.lieu, Literal(str(comm_enterrement).strip())))

        g.add((event_uri, TEMP.before, inhumation_event_uri))
        count_inhumation += 1
        g.add((inhumation_event_uri, PROP_temporal_after, event_uri))

    additional_counts = add_additional_typed_events(
        g,
        person_event_pairs,
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "italie_cpr",
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

    # SOURCE (structure conservee)
    source_val = row.get("Source", "") or row.get("source", "")
    if is_missing(source_val):
        source_val = row.get("Struttura", "")
    if source_val and not is_missing(source_val):
        source_str = str(source_val).strip()
        source_uri = DATA["italie_Source_%d" % (idx + 1)]
        g.add((source_uri, RDF.type, F.Source))
        source_norm = norm(source_str)
        # Dans ce dataset, les sources de type camp/centre doivent etre
        # classees en CivilSociety plutot qu'en document officiel.
        if re.search(r"\b(cpr|cpt|cie|camp|centro)\b", source_norm):
            source_category = "civil_society"
        else:
            source_category = infer_source_category_key(source_str)
        if source_category == "family":
            g.add((source_uri, RDF.type, F.Family))
        elif source_category == "media":
            g.add((source_uri, RDF.type, F.Media))
        elif source_category == "civil_society":
            g.add((source_uri, RDF.type, F.CivilSociety))
        elif source_category == "death_certificate":
            g.add((source_uri, RDF.type, F.DeathCertificate))
        elif source_category == "official_document":
            g.add((source_uri, RDF.type, F.OfficialDocument))
        else:
            # Fallback explicite: une source doit appartenir a l'une des 6 classes.
            g.add((source_uri, RDF.type, F.OtherOfficialDocument))

        if source_str.lower().startswith("http"):
            g.add((source_uri, PROP_hasWebLink, Literal(source_str)))
        else:
            g.add((source_uri, RDFS.label, Literal(source_str)))
            g.add((source_uri, PROP_hasComment, Literal(source_str)))

        g.add((event_uri, PROP_sourcedBy, source_uri))
        count_sources += 1


# --------------------- Resume et sortie ------------------
count_geom_propagated = propagate_geometry_to_sibling_events(g, F, GEO, RDF, Literal, "italie_cpr")
count_event_country_from_geometry = add_event_country_from_geometry(g, F, DATA, GEO, RDF, RDFS, Literal, "italie_cpr")
g.serialize(destination=OUTPUT_TTL, format="turtle")
if ALLOW_LIVE_GEOCODING:
    save_geocode_cache(GEOCODE_CACHE_PATH, geocode_cache)

print("\n" + "=" * 60)
print("Import Italie_CPR complete.")
print("=" * 60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created: {count_death_events}")
print(f"Injury events created: {count_injury_events}")
print(f"Missing events created: {count_missing_events}")
print(f"Transport individuals created: {count_transports}")
print(f"Embark events created: {count_embark}")
print(f"Collective events created: {count_collective_events}")
print(f"Repatriation events created: {count_repatriation}")
print(f"Inhumation events created: {count_inhumation}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Sources created: {count_sources}")
print(f"Death certificates created: {count_death_certificates}")
print("\nCause deces - mapping avec thesaurus:")
print(f"  - Matched to thesaurus URI: {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"  - DeathNature linked: {count_nature_mapped}")
print("\nDetection d'accidents de circulation:")
print(f"  - Accidents detectes (percute/renverse/accident): {count_traffic_accidents}")
print(f"  - Moyen de transport identifie: {count_transport_identified}")
print("\nGeocodage Struttura:")
print(f"  - Geocodages reussis: {count_geocode_success}")
print(f"  - Geocodages non resolus: {count_geocode_failed}")
print("  - Rate limit detecte: non bloquant (style Alpes)")
print(f"  - Mode geocodage: {'live' if ALLOW_LIVE_GEOCODING else 'cache-only'}")
print(f"Geometry propagated to siblings: {count_geom_propagated}")
print(f"Event countries from geometry: {count_event_country_from_geometry}")
print("=" * 60)
print(f"Output written to: {OUTPUT_TTL}")


