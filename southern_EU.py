def find_nearest_church_from_osm_overpass(lat, lon, max_distance_km=10.0):
    """Retourne la plus proche église (amenity=church) autour des coordonnées via Overpass."""
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return None
    if not math.isfinite(lat) or not math.isfinite(lon):
        return None
    radius_m = int(max(1.0, float(max_distance_km)) * 1000.0)
    overpass_query = (
        f"[out:json][timeout:25];"
        f"(node[\"amenity\"=\"church\"](around:{radius_m},{lat},{lon});"
        f" way[\"amenity\"=\"church\"](around:{radius_m},{lat},{lon});"
        f" relation[\"amenity\"=\"church\"](around:{radius_m},{lat},{lon}););"
        "out center tags;"
    )
    data = urllib.parse.urlencode({"data": overpass_query}).encode("utf-8")
    overpass_endpoints = (
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.fr/api/interpreter",
    )
    for endpoint in overpass_endpoints:
        req = urllib.request.Request(
            endpoint,
            data=data,
            headers={
                "User-Agent": "frontlet_southern_eu_church_locator/1.0",
                "Accept": "application/json",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                payload = resp.read().decode("utf-8", errors="replace")
            parsed = json.loads(payload)
        except Exception:
            continue
        elements = parsed.get("elements", []) if isinstance(parsed, dict) else []
        best = None
        for elem in elements:
            if not isinstance(elem, dict):
                continue
            elat = elem.get("lat")
            elon = elem.get("lon")
            if elat is None or elon is None:
                center = elem.get("center") if isinstance(elem.get("center"), dict) else None
                if center is not None:
                    elat = center.get("lat")
                    elon = center.get("lon")
            try:
                cand_lat = float(elat)
                cand_lon = float(elon)
            except Exception:
                continue
            if not math.isfinite(cand_lat) or not math.isfinite(cand_lon):
                continue
            distance_km = haversine_km(lat, lon, cand_lat, cand_lon)
            tags = elem.get("tags") if isinstance(elem.get("tags"), dict) else {}
            name = str(tags.get("name", "")).strip()
            candidate = {
                "lat": cand_lat,
                "lon": cand_lon,
                "distance_km": distance_km,
                "name": name if name else "church",
                "amenity": "church",
            }
            if best is None or candidate["distance_km"] < best["distance_km"]:
                best = candidate
        if best is not None:
            return best
    return None
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
import difflib
import json
import random
import urllib.parse
import urllib.request
import pycountry
try:
    import reverse_geocoder as rg
except Exception:
    rg = None
from geopy.geocoders import ArcGIS, Nominatim, Photon
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
    propagate_geometry_to_sibling_events,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH   = "frontletOnto.ttl"
THES_PATH   = "frontletThesaurus.ttl"
CSV_PATH    = "southern_eu/ue_sudMorts.csv"
OUTPUT_TTL  = "southern_eu/frontlet_import_output.ttl"
MAPPING_PATH = "southern_eu/mappingUE_SudThesaurusCauseMort.csv"
GEOCODE_CACHE_PATH      = "southern_eu/geocode_cache.json"
WKT_CACHE_PATH          = "southern_eu/wkt_cache.json"
GEOCODE_MIN_DELAY_SECONDS   = 0.0
GEOCODE_429_BACKOFF_SECONDS = 5.0
GEOCODE_MAX_429_RETRIES     = 1
GEOCODE_REQUEST_TIMEOUT_SECONDS = 2
GEOCODER_PROVIDER_ORDER = ("arcgis",)
GEOCODER_FAILURE_THRESHOLD = 3
GEOCODER_DISABLE_SECONDS = 1800
OVERPASS_REQUEST_TIMEOUT_SECONDS = 6
OVERPASS_FAILURE_COOLDOWN_SECONDS = 900
USE_OVERPASS_CEMETERY_PROVIDER = False
ENABLE_NON_OSM_CEMETERY_POI_LOOKUP = True
MAX_NON_OSM_CEMETERY_POI_PER_RUN = 10
MAX_FORCED_NON_OSM_CEMETERY_POI_PER_RUN = 20
MAX_FORCED_OVERPASS_CEMETERY_PER_RUN = 6
MAX_NON_OSM_CHURCH_POI_PER_RUN = None  # Pas de limite sur le fallback église
WHERE_BURIED_CENTROID_REFINEMENT_KM = 3.0
MAX_REMOTE_GEOCODE_SECONDS_PER_RUN = 900
BURIAL_LOCATION_OVERRIDES = {
    3170: "Arrecife, Spain",
    3177: "Arrecife, Spain",
}
BURIAL_COORDINATE_OVERRIDES = {
    1339: {
        "lat": 15.3500426,
        "lon": 38.9676609,
        "name": "Asmara War Cemetery",
    },
    1342: {
        "lat": 15.3500426,
        "lon": 38.9676609,
        "name": "Asmara War Cemetery",
    },
    1518: {
        "lat": 15.3500426,
        "lon": 38.9676609,
        "name": "Asmara War Cemetery",
    },
    3025: {
        "lat": 12.6423039,
        "lon": -8.0052729,
        "name": "Bamako European Cemetery",
    },
    3170: {
        "lat": 28.984952596662,
        "lon": -13.553239388998,
        "name": "Camino al Cementerio, Arrecife, Lanzarote, Spain",
    },
    3177: {
        "lat": 28.984952596662,
        "lon": -13.553239388998,
        "name": "Camino al Cementerio, Arrecife, Lanzarote, Spain",
    },
}

# Compat mode: mettre ROW_LIMIT a None pour traiter tout le CSV.

ROW_LIMIT = None
ENABLE_GEOCODING = False  # Désactive tout géocodage pour accélérer
ENABLE_INHUMATION_GEOCODING = False
USE_TEXTUAL_GEO_FALLBACK = False
FAST_POINT_WKT_FOR_GEOCODED = True
USE_NOMINATIM_FALLBACK = False
ENABLE_ARCGIS_FALLBACK = False
ENABLE_REMOTE_GEOCODER = False
RETRY_NOT_FOUND_CACHE_WITH_REMOTE = False
MAX_NOT_FOUND_REMOTE_RETRIES_PER_RUN = 5000
NOT_FOUND_RETRY_COOLDOWN_SECONDS = 0
STRICT_COUNTRY_CHECK_FOR_ALL_GEOCODES = False
STRICT_COUNTRY_CHECK_FOR_AMBIGUOUS_GEOCODES = False
ULTRA_FAST_COUNTRY_FALLBACK_GEOCODING = False
STRICT_LITERAL_CAUSE = False
ENABLE_TEXTUAL_MISSING_INFERENCE_IF_NONE = True
RANDOM_GEOCODE_ROW_LIMIT = None
GEOCODE_RANDOM_SEED = 42
ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED = True

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


def normalize_where_buried_text(where_buried, city_val):
    if is_missing(where_buried) or is_missing(city_val):
        return where_buried

    parts = [part.strip() for part in str(where_buried).split(",") if part.strip()]
    if not parts:
        return where_buried

    burial_place = parts[0]
    if norm(burial_place) == norm(city_val):
        return ", ".join(parts)

    ratio = difflib.SequenceMatcher(None, norm(burial_place), norm(city_val)).ratio()
    if ratio < 0.84:
        return ", ".join(parts)

    parts[0] = str(city_val).strip()
    return ", ".join(parts)


def has_cemetery_signal(value):
    text = norm(value)
    if not text:
        return False
    cemetery_markers = (
        "cimiter", "cemeter", "graveyard", "grave yard", "gorostha", "cementerio",
        "necropol", "cemetery",
    )
    return any(marker in text for marker in cemetery_markers)


def has_diplomatic_signal(value):
    text = norm(value)
    if not text:
        return False
    diplomatic_markers = (
        "embassy", "ambassade", "consulat", "consulate", "high commission",
        "mission diplomatique", "diplomatic mission",
    )
    return any(marker in text for marker in diplomatic_markers)


def has_church_signal(value):
    text = norm(value)
    if not text:
        return False
    church_markers = (
        "church", "eglise", "église", "chiesa", "iglesia", "chapel",
        "cathedral", "paroisse", "parish", "basilica",
    )
    return any(marker in text for marker in church_markers)


def sanitize_where_buried_diplomatic_text(where_buried, city_val, country_val):
    if is_missing(where_buried):
        return where_buried
    raw = str(where_buried).strip()
    if not has_diplomatic_signal(raw):
        return raw

    parts = [part.strip() for part in raw.split(",") if part.strip()]
    cleaned_parts = [part for part in parts if not has_diplomatic_signal(part)]
    if cleaned_parts:
        return ", ".join(cleaned_parts)

    fallback_parts = []
    if not is_missing(city_val):
        fallback_parts.append(str(city_val).strip())
    if not is_missing(country_val):
        fallback_parts.append(str(country_val).strip())
    return ", ".join(fallback_parts) if fallback_parts else raw


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
geolocator = Photon(user_agent="frontlet_southern_eu_geocoder", timeout=10)
arcgis_geolocator = ArcGIS(timeout=10)
fallback_geolocator = Nominatim(user_agent="frontlet_southern_eu_geocoder_fallback", timeout=10)
NOMINATIM_RATE_LIMITED = False
LAST_GEOCODE_REQUEST_TS    = 0.0
WKT_CACHE = {}
COORD_COUNTRY_CACHE = {}
EXPECTED_COUNTRY_CACHE = {}
NOT_FOUND_REMOTE_RETRY_COUNT = 0
REMOTE_GEOCODE_DEADLINE_TS = None
ALLOWED_RANDOM_GEO_ROW_NUMS = set()
OVERPASS_CONSECUTIVE_FAILURES = 0
OVERPASS_DISABLED_UNTIL_TS = 0.0
GEOCODER_CONSECUTIVE_FAILURES = {"photon": 0, "arcgis": 0, "nominatim": 0}
GEOCODER_DISABLED_UNTIL_TS = {"photon": 0.0, "arcgis": 0.0, "nominatim": 0.0}
NON_OSM_CEMETERY_POI_LOOKUP_COUNT = 0
FORCED_NON_OSM_CEMETERY_POI_LOOKUP_COUNT = 0
FORCED_OVERPASS_CEMETERY_LOOKUP_COUNT = 0
NON_OSM_CHURCH_POI_LOOKUP_COUNT = 0
COUNTRY_NODE_CACHE = {}
COUNTRY_NAME_INDEX = None
COUNTRY_COORD_SUM = {}
COUNTRY_COORD_COUNT = {}
LOCAL_GEO_CACHE_INDEX = None
COUNTRY_DEFAULT_COORDS = {
    "ITA": (41.9028, 12.4964),
    "ESP": (40.4168, -3.7038),
    "GRC": (37.9838, 23.7275),
    "MLT": (35.8989, 14.5146),
    "MAR": (34.0209, -6.8416),
    "DZA": (36.7538, 3.0588),
    "TUN": (36.8065, 10.1815),
    "LBY": (32.8872, 13.1913),
    "EGY": (30.0444, 31.2357),
    "TUR": (39.9334, 32.8597),
}


def _build_country_name_index():
    index = {}
    for c in pycountry.countries:
        for attr in ("name", "official_name", "common_name"):
            value = getattr(c, attr, None)
            if not value:
                continue
            key = norm(value)
            if key:
                index[key] = c
    return index


def _geo_tokens(text):
    if is_missing(text):
        return set()
    words = re.findall(r"[a-z0-9]+", norm(text))
    return {w for w in words if len(w) >= 3}


def _build_local_geo_cache_index(geocode_cache):
    rows = []
    for key, value in geocode_cache.items():
        if not isinstance(value, dict):
            continue
        if "lat" not in value or "lon" not in value:
            continue
        try:
            lat = float(value["lat"])
            lon = float(value["lon"])
        except Exception:
            continue
        if str(value.get("provider") or "").strip().lower() == "local_cache_fuzzy":
            continue
        if not math.isfinite(lat) or not math.isfinite(lon):
            continue
        query = str(value.get("query") or key)
        rows.append({
            "query": query,
            "query_norm": norm(query),
            "tokens": _geo_tokens(query),
            "lat": lat,
            "lon": lon,
            "cc": str(value.get("cc") or "").upper() or None,
        })
    return rows


def local_cache_geocode_fallback(location_str, geocode_cache, expected_country_codes=None):
    global LOCAL_GEO_CACHE_INDEX

    if LOCAL_GEO_CACHE_INDEX is None:
        LOCAL_GEO_CACHE_INDEX = _build_local_geo_cache_index(geocode_cache)

    q_norm = norm(location_str)
    q_tokens = _geo_tokens(location_str)
    if not q_norm:
        return None, None, None

    best = None
    best_score = -1.0
    for row in LOCAL_GEO_CACHE_INDEX:
        if expected_country_codes:
            row_cc = row.get("cc")
            if row_cc and row_cc not in expected_country_codes:
                continue
            if row_cc is None and not coords_match_expected_country(
                row["lat"],
                row["lon"],
                expected_country_codes,
                strict_required=True,
            ):
                continue

        overlap = 0
        if q_tokens and row["tokens"]:
            overlap = len(q_tokens & row["tokens"])

        # Fast textual similarity for typo/noise tolerance.
        ratio = difflib.SequenceMatcher(None, q_norm, row["query_norm"]).ratio()
        score = overlap * 3.0 + ratio
        if score > best_score:
            best_score = score
            best = row

    if best is None:
        return None, None, None

    # Guardrail: avoid unrelated matches.
    if best_score < 1.2:
        return None, None, None

    return best["lat"], best["lon"], best.get("cc")


def _country_iso3_from_uri(country_uri):
    if country_uri is None:
        return None
    m = re.search(r"_Country_([A-Z]{3})$", str(country_uri))
    if m:
        return m.group(1)
    return None


def update_country_coord_stats(country_uri, lat, lon):
    iso3 = _country_iso3_from_uri(country_uri)
    if not iso3:
        return
    COUNTRY_COORD_SUM[iso3] = (
        COUNTRY_COORD_SUM.get(iso3, (0.0, 0.0))[0] + float(lat),
        COUNTRY_COORD_SUM.get(iso3, (0.0, 0.0))[1] + float(lon),
    )
    COUNTRY_COORD_COUNT[iso3] = COUNTRY_COORD_COUNT.get(iso3, 0) + 1


def get_country_fallback_coord(country_uri):
    iso3 = _country_iso3_from_uri(country_uri)
    if not iso3:
        return None, None

    cnt = COUNTRY_COORD_COUNT.get(iso3, 0)
    if cnt > 0 and iso3 in COUNTRY_COORD_SUM:
        s_lat, s_lon = COUNTRY_COORD_SUM[iso3]
        return (s_lat / cnt), (s_lon / cnt)

    return COUNTRY_DEFAULT_COORDS.get(iso3, (None, None))


def extract_country_code_from_location(location):
    """Extract ISO alpha-2 country code from geocoder raw payload when available."""
    try:
        raw = getattr(location, "raw", None)
        if not isinstance(raw, dict):
            return None

        candidates = []
        props = raw.get("properties")
        if isinstance(props, dict):
            candidates.extend([
                props.get("countrycode"),
                props.get("country_code"),
                props.get("iso2"),
            ])

        addr = raw.get("address")
        if isinstance(addr, dict):
            candidates.extend([
                addr.get("country_code"),
                addr.get("countrycode"),
            ])

        candidates.extend([
            raw.get("countrycode"),
            raw.get("country_code"),
            raw.get("iso2"),
        ])

        for candidate in candidates:
            cc = str(candidate or "").strip().upper()
            if re.fullmatch(r"[A-Z]{2}", cc):
                return cc
    except Exception:
        return None
    return None


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


def resolve_expected_country_codes(country_value):
    """Resolve expected ISO alpha-2 country codes from CSV Country value."""
    if is_missing(country_value):
        return set()

    key = norm(country_value)
    cached = EXPECTED_COUNTRY_CACHE.get(key)
    if cached is not None:
        return set(cached)

    result = set()
    raw = str(country_value).strip()
    parts = [p.strip() for p in re.split(r"[,;/|]", raw) if p.strip()]
    if not parts:
        parts = [raw]

    for part in parts:
        token = re.sub(r"[^A-Za-z0-9]", "", part).upper()
        cc = None
        try:
            if re.fullmatch(r"[A-Z]{2}", token):
                cc = pycountry.countries.get(alpha_2=token)
            elif re.fullmatch(r"[A-Z]{3}", token):
                cc = pycountry.countries.get(alpha_3=token)
        except Exception:
            cc = None

        if cc is None:
            try:
                matches = pycountry.countries.search_fuzzy(part)
                if matches:
                    cc = matches[0]
            except Exception:
                cc = None

        if cc is not None and getattr(cc, "alpha_2", None):
            result.add(cc.alpha_2.upper())

    EXPECTED_COUNTRY_CACHE[key] = sorted(result)
    return result


def is_country_only_location(value):
    """Return True when a free-text location is just a country name/code."""
    if is_missing(value):
        return False

    raw = re.sub(r"\s+", " ", str(value)).strip(" ,;")
    if not raw:
        return False

    parts = [p.strip() for p in re.split(r"[,;/|]", raw) if p.strip()]
    if len(parts) != 1:
        return False

    part = parts[0]
    token = re.sub(r"[^A-Za-z0-9]", "", part).upper()
    if re.fullmatch(r"[A-Z]{2}", token) or re.fullmatch(r"[A-Z]{3}", token):
        return True

    global COUNTRY_NAME_INDEX
    if COUNTRY_NAME_INDEX is None:
        COUNTRY_NAME_INDEX = _build_country_name_index()
    return norm(part) in COUNTRY_NAME_INDEX


def extract_specific_sea_place(candidate):
    """Extract a non-generic place from strings like 'sea, Diapori, Syros'."""
    if is_missing(candidate):
        return None

    text = str(candidate).strip()
    if not text:
        return None

    match = re.match(r"^(?:sea|high seas|at sea)\s*[,;:-]?\s*(.+)$", text, flags=re.IGNORECASE)
    if not match:
        return None

    remainder = match.group(1).strip(" ,;")
    if not remainder:
        return None

    remainder_norm = norm(remainder)
    if remainder_norm in {"sea", "at sea", "high seas", "mediterranean sea"}:
        return None
    return remainder


def coord_country_code(lat, lon):
    """Return ISO alpha-2 country code for coordinates when available."""
    cache_key = f"{round(float(lat), 3)}|{round(float(lon), 3)}"
    cached = COORD_COUNTRY_CACHE.get(cache_key)
    if cached is not None:
        return cached

    if rg is None:
        COORD_COUNTRY_CACHE[cache_key] = None
        return None

    try:
        res = rg.search((float(lat), float(lon)), mode=1)
        cc = None
        if res and isinstance(res, list):
            cc = (res[0].get("cc") or "").upper() if isinstance(res[0], dict) else None
        COORD_COUNTRY_CACHE[cache_key] = cc or None
        return cc or None
    except Exception:
        COORD_COUNTRY_CACHE[cache_key] = None
        return None


def coords_match_expected_country(lat, lon, expected_country_codes, strict_required=False):
    """Validate that coordinates belong to expected Country when resolvable."""
    if not expected_country_codes:
        return True
    cc = coord_country_code(lat, lon)
    if cc is None:
        if strict_required:
            return False
        return True
    return cc in expected_country_codes


def canonicalize_geo_query(query):
    """Normalize noisy repeated location labels to reduce duplicate geocoding/WKT work."""
    if is_missing(query):
        return None

    q = re.sub(r"\s+", " ", str(query)).strip(" ,;")
    if not q:
        return None

    parts = [p.strip() for p in q.split(",") if p.strip()]
    if not parts:
        return q

    first_part = norm(parts[0])
    water_prefixes = (
        "sea",
        "high seas",
        "mediterranean sea",
        "on board",
        "onboard",
    )
    if any(first_part.startswith(prefix) for prefix in water_prefixes) and len(parts) >= 2:
        return f"sea, {parts[-1]}"

    return q


def requires_strict_country_check(query):
    """Use costly reverse-country validation only for ambiguous/water locations."""
    if STRICT_COUNTRY_CHECK_FOR_ALL_GEOCODES:
        return True
    if not STRICT_COUNTRY_CHECK_FOR_AMBIGUOUS_GEOCODES:
        return False
    if is_missing(query):
        return False

    q_norm = norm(query)
    if q_norm.startswith("sea") or q_norm.startswith("high seas"):
        return True
    if " mediterranean" in q_norm or " aegean" in q_norm or " ionian" in q_norm:
        return True
    if " on board" in q_norm or " offshore" in q_norm:
        return True
    return False


def geocode_location(location_str, geocode_cache, max_retries=1, expected_country_codes=None):
    """Géocode une chaîne ville+pays et retourne (lat, lon) ou (None, None)."""
    global NOMINATIM_RATE_LIMITED, NOT_FOUND_REMOTE_RETRY_COUNT, REMOTE_GEOCODE_DEADLINE_TS
    global GEOCODER_CONSECUTIVE_FAILURES, GEOCODER_DISABLED_UNTIL_TS

    if is_missing(location_str):
        return None, None

    location_str = canonicalize_geo_query(location_str) or str(location_str).strip()
    strict_country_check = requires_strict_country_check(location_str)
    cache_key = norm(location_str)
    if expected_country_codes:
        cache_key += "|cc:" + "-".join(sorted(expected_country_codes))

    cached = geocode_cache.get(cache_key)
    trust_cached_local_fuzzy = not (
        isinstance(cached, dict)
        and str(cached.get("provider") or "").strip().lower() == "local_cache_fuzzy"
        and (norm(location_str).startswith("cemetery") or is_country_only_location(location_str))
    )
    if cached == "NOT_FOUND":
        # Legacy cache entries from no-remote runs should be retried when remote geocoder is enabled.
        if not (ENABLE_REMOTE_GEOCODER and RETRY_NOT_FOUND_CACHE_WITH_REMOTE):
            return None, None
        if NOT_FOUND_REMOTE_RETRY_COUNT >= MAX_NOT_FOUND_REMOTE_RETRIES_PER_RUN:
            return None, None
        NOT_FOUND_REMOTE_RETRY_COUNT += 1
    if isinstance(cached, dict) and cached.get("status") == "NOT_FOUND":
        if not (ENABLE_REMOTE_GEOCODER and RETRY_NOT_FOUND_CACHE_WITH_REMOTE):
            return None, None
        try:
            last_try_ts = float(cached.get("last_try_ts") or 0.0)
        except Exception:
            last_try_ts = 0.0
        if (time.time() - last_try_ts) < NOT_FOUND_RETRY_COOLDOWN_SECONDS:
            return None, None
        if NOT_FOUND_REMOTE_RETRY_COUNT >= MAX_NOT_FOUND_REMOTE_RETRIES_PER_RUN:
            return None, None
        NOT_FOUND_REMOTE_RETRY_COUNT += 1
    if trust_cached_local_fuzzy and isinstance(cached, dict) and "lat" in cached and "lon" in cached:
        try:
            lat_cached = float(cached["lat"])
            lon_cached = float(cached["lon"])
            cached_cc = (cached.get("cc") or "").upper() if isinstance(cached.get("cc"), str) else None
            if not expected_country_codes:
                return lat_cached, lon_cached
            if cached_cc:
                if cached_cc in expected_country_codes:
                    return lat_cached, lon_cached
            elif coords_match_expected_country(
                lat_cached,
                lon_cached,
                expected_country_codes,
                strict_required=ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED,
            ):
                return lat_cached, lon_cached
        except Exception:
            pass

    if not ENABLE_REMOTE_GEOCODER:
        if norm(location_str).startswith("cemetery"):
            return None, None
        lat_local, lon_local, cc_local = local_cache_geocode_fallback(
            location_str,
            geocode_cache,
            expected_country_codes=expected_country_codes,
        )
        if lat_local is not None and lon_local is not None:
            geocode_cache[cache_key] = {
                "lat": float(lat_local),
                "lon": float(lon_local),
                "cc": cc_local,
                "query": location_str,
                "provider": "local_cache_fuzzy",
            }
            return float(lat_local), float(lon_local)
        return None, None

    if REMOTE_GEOCODE_DEADLINE_TS is None:
        if MAX_REMOTE_GEOCODE_SECONDS_PER_RUN is not None:
            REMOTE_GEOCODE_DEADLINE_TS = time.time() + MAX_REMOTE_GEOCODE_SECONDS_PER_RUN
    if REMOTE_GEOCODE_DEADLINE_TS is not None and time.time() >= REMOTE_GEOCODE_DEADLINE_TS:
        return None, None

    provider_map = {
        "photon": geolocator,
        "arcgis": arcgis_geolocator,
        "nominatim": fallback_geolocator,
    }
    providers = []
    now_ts = time.time()
    for provider_name in GEOCODER_PROVIDER_ORDER:
        if provider_name not in provider_map:
            continue
        if provider_name == "arcgis" and not ENABLE_ARCGIS_FALLBACK:
            continue
        if provider_name == "nominatim":
            if not USE_NOMINATIM_FALLBACK or NOMINATIM_RATE_LIMITED:
                continue
        disabled_until = float(GEOCODER_DISABLED_UNTIL_TS.get(provider_name, 0.0) or 0.0)
        if disabled_until > now_ts:
            continue
        providers.append((provider_name, provider_map[provider_name]))

    for provider_name, provider in providers:
        for attempt in range(max_retries):
            try:
                throttle_geocode_requests()
                location = provider.geocode(location_str, timeout=GEOCODE_REQUEST_TIMEOUT_SECONDS)
                if location:
                    lat = float(location.latitude)
                    lon = float(location.longitude)
                    cc = extract_country_code_from_location(location)
                    if cc is None and expected_country_codes and (
                        strict_country_check or ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED
                    ):
                        cc = coord_country_code(lat, lon)
                    if expected_country_codes:
                        if cc is None and ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED:
                            continue
                        if cc is not None and cc not in expected_country_codes:
                            continue
                    geocode_cache[cache_key] = {
                        "lat": lat,
                        "lon": lon,
                        "cc": cc,
                        "query": location_str,
                        "provider": provider_name,
                    }
                    GEOCODER_CONSECUTIVE_FAILURES[provider_name] = 0
                    GEOCODER_DISABLED_UNTIL_TS[provider_name] = 0.0
                    return lat, lon
                break
            except GeocoderTimedOut:
                GEOCODER_CONSECUTIVE_FAILURES[provider_name] = GEOCODER_CONSECUTIVE_FAILURES.get(provider_name, 0) + 1
                if GEOCODER_CONSECUTIVE_FAILURES[provider_name] >= GEOCODER_FAILURE_THRESHOLD:
                    GEOCODER_DISABLED_UNTIL_TS[provider_name] = time.time() + float(GEOCODER_DISABLE_SECONDS)
                if attempt < max_retries - 1:
                    continue
                break
            except GeocoderServiceError as e:
                if is_http_429_error(e):
                    if provider_name == "nominatim":
                        NOMINATIM_RATE_LIMITED = True
                        break
                    for retry in range(GEOCODE_MAX_429_RETRIES):
                        time.sleep(GEOCODE_429_BACKOFF_SECONDS * (retry + 1))
                        try:
                            throttle_geocode_requests()
                            location = provider.geocode(location_str, timeout=GEOCODE_REQUEST_TIMEOUT_SECONDS)
                            if location:
                                lat = float(location.latitude)
                                lon = float(location.longitude)
                                cc = extract_country_code_from_location(location)
                                if cc is None and expected_country_codes and (
                                    strict_country_check or ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED
                                ):
                                    cc = coord_country_code(lat, lon)
                                if expected_country_codes:
                                    if cc is None and ENFORCE_COUNTRY_MATCH_WHEN_PROVIDED:
                                        continue
                                    if cc is not None and cc not in expected_country_codes:
                                        continue
                                geocode_cache[cache_key] = {
                                    "lat": lat,
                                    "lon": lon,
                                    "cc": cc,
                                    "query": location_str,
                                    "provider": provider_name,
                                }
                                GEOCODER_CONSECUTIVE_FAILURES[provider_name] = 0
                                GEOCODER_DISABLED_UNTIL_TS[provider_name] = 0.0
                                return lat, lon
                        except Exception:
                            continue
                GEOCODER_CONSECUTIVE_FAILURES[provider_name] = GEOCODER_CONSECUTIVE_FAILURES.get(provider_name, 0) + 1
                if GEOCODER_CONSECUTIVE_FAILURES[provider_name] >= GEOCODER_FAILURE_THRESHOLD:
                    GEOCODER_DISABLED_UNTIL_TS[provider_name] = time.time() + float(GEOCODER_DISABLE_SECONDS)
                break
            except Exception as e:
                if is_http_429_error(e) and provider_name == "nominatim":
                    NOMINATIM_RATE_LIMITED = True
                GEOCODER_CONSECUTIVE_FAILURES[provider_name] = GEOCODER_CONSECUTIVE_FAILURES.get(provider_name, 0) + 1
                if GEOCODER_CONSECUTIVE_FAILURES[provider_name] >= GEOCODER_FAILURE_THRESHOLD:
                    GEOCODER_DISABLED_UNTIL_TS[provider_name] = time.time() + float(GEOCODER_DISABLE_SECONDS)
                break

    geocode_cache[cache_key] = {
        "status": "NOT_FOUND",
        "last_try_ts": time.time(),
        "query": location_str,
    }
    return None, None


def find_cemetery_poi_non_osm(where_buried_text, geocode_cache, expected_country_codes=None, force_lookup=False):
    """Find a cemetery POI from Where_buried using non-OSM providers (ArcGIS).

    Returns dict(lat, lon, name, distance_km, amenity) or None.
    """
    global NON_OSM_CEMETERY_POI_LOOKUP_COUNT, FORCED_NON_OSM_CEMETERY_POI_LOOKUP_COUNT

    if not ENABLE_NON_OSM_CEMETERY_POI_LOOKUP or is_missing(where_buried_text):
        return None

    wb_text = canonicalize_geo_query(str(where_buried_text).strip())
    if is_missing(wb_text):
        return None

    wb_norm = norm(wb_text)
    priority_lookup = "gela" in wb_norm
    if (
        not priority_lookup
        and not force_lookup
        and MAX_NON_OSM_CEMETERY_POI_PER_RUN is not None
        and NON_OSM_CEMETERY_POI_LOOKUP_COUNT >= int(MAX_NON_OSM_CEMETERY_POI_PER_RUN)
    ):
        return None
    if (
        force_lookup
        and MAX_FORCED_NON_OSM_CEMETERY_POI_PER_RUN is not None
        and FORCED_NON_OSM_CEMETERY_POI_LOOKUP_COUNT >= int(MAX_FORCED_NON_OSM_CEMETERY_POI_PER_RUN)
    ):
        return None

    cache_key = f"poi_cemetery|{norm(wb_text)}"
    if expected_country_codes:
        cache_key += "|cc:" + "-".join(sorted(expected_country_codes))

    cached = geocode_cache.get(cache_key)
    if isinstance(cached, dict) and "lat" in cached and "lon" in cached:
        try:
            cached_name = str(cached.get("name") or "")
            if has_diplomatic_signal(cached_name):
                raise ValueError("cached cemetery POI diplomatic mismatch")
            c_lat = float(cached["lat"])
            c_lon = float(cached["lon"])
            if expected_country_codes and not coords_match_expected_country(
                c_lat,
                c_lon,
                expected_country_codes,
                strict_required=True,
            ):
                raise ValueError("cached cemetery POI country mismatch")
            return {
                "lat": c_lat,
                "lon": c_lon,
                "name": cached_name if cached_name else f"cemetery, {wb_text}",
                "distance_km": 0.0,
                "amenity": "cemetery",
            }
        except Exception:
            pass
    if isinstance(cached, dict) and cached.get("status") == "NOT_FOUND":
        if not priority_lookup and not force_lookup:
            return None

    ref_lat, ref_lon = geocode_location(
        wb_text,
        geocode_cache,
        expected_country_codes=expected_country_codes,
    )

    poi_timeout = max(5, int(GEOCODE_REQUEST_TIMEOUT_SECONDS))

    # Fast probe: one direct Italian/Latinate cemetery query often resolves city cemeteries precisely.
    try:
        probe = arcgis_geolocator.geocode(
            f"cimitero, {wb_text}",
            timeout=poi_timeout,
            exactly_one=True,
        )
    except Exception:
        probe = None
    if probe is not None:
        try:
            p_lat = float(probe.latitude)
            p_lon = float(probe.longitude)
            if math.isfinite(p_lat) and math.isfinite(p_lon):
                if expected_country_codes and not coords_match_expected_country(
                    p_lat,
                    p_lon,
                    expected_country_codes,
                    strict_required=True,
                ):
                    raise ValueError("probe cemetery POI country mismatch")
                p_address = str(getattr(probe, "address", "") or "").strip()
                p_norm = norm(p_address)
                if has_diplomatic_signal(p_norm):
                    raise ValueError("probe cemetery POI diplomatic mismatch")
                if any(k in p_norm for k in ("cimiter", "cemeter", "graveyard")):
                    geocode_cache[cache_key] = {
                        "lat": p_lat,
                        "lon": p_lon,
                        "name": p_address if p_address else f"cemetery, {wb_text}",
                        "query": wb_text,
                        "provider": "arcgis_poi_probe",
                    }
                    return {
                        "lat": p_lat,
                        "lon": p_lon,
                        "name": p_address if p_address else f"cemetery, {wb_text}",
                        "distance_km": 0.0,
                        "amenity": "cemetery",
                    }
        except Exception:
            pass

    queries = [
        f"cemetery, {wb_text}",
        f"cimitero, {wb_text}",
        f"graveyard, {wb_text}",
    ]

    NON_OSM_CEMETERY_POI_LOOKUP_COUNT += 1
    if force_lookup:
        FORCED_NON_OSM_CEMETERY_POI_LOOKUP_COUNT += 1

    best = None
    tokens = _build_cemetery_name_tokens(wb_text)

    for query in queries:
        try:
            results = arcgis_geolocator.geocode(
                query,
                timeout=poi_timeout,
                exactly_one=False,
            )
        except Exception:
            results = None

        if not results:
            continue
        if not isinstance(results, list):
            results = [results]

        # Si aucun cimetière n'est trouvé, on place systématiquement le point sur l'église de la ville (fallback)
        # Cette stratégie permet de garantir que l'inhumation est toujours localisée sur un lieu religieux pertinent.
        for loc in results[:8]:
            try:
                lat = float(loc.latitude)
                lon = float(loc.longitude)
            except Exception:
                continue
            if not math.isfinite(lat) or not math.isfinite(lon):
                continue

            cc = extract_country_code_from_location(loc)
            if expected_country_codes and cc is not None and cc not in expected_country_codes:
                continue
            if expected_country_codes and not coords_match_expected_country(
                lat,
                lon,
                expected_country_codes,
                strict_required=True,
            ):
                continue

            address = str(getattr(loc, "address", "") or "").strip()
            addr_norm = norm(address)
            if has_diplomatic_signal(addr_norm):
                continue
            score = 0

            if any(k in addr_norm for k in ("cimiter", "cemeter", "graveyard")):
                score += 50
            for tok in tokens:
                if tok in addr_norm:
                    score += 8

            distance_km = 0.0
            if ref_lat is not None and ref_lon is not None:
                distance_km = haversine_km(float(ref_lat), float(ref_lon), lat, lon)
                score += max(0.0, 30.0 - min(distance_km, 30.0))

            candidate = {
                "lat": lat,
                "lon": lon,
                "name": address if address else f"cemetery, {wb_text}",
                "distance_km": distance_km,
                "amenity": "cemetery",
                "score": score,
            }

            if (
                best is None
                or candidate["score"] > best["score"]
                or (
                    candidate["score"] == best["score"]
                    and candidate["distance_km"] < best["distance_km"]
                )
            ):
                best = candidate

    if best is None:
        geocode_cache[cache_key] = {
            "status": "NOT_FOUND",
            "last_try_ts": time.time(),
            "query": wb_text,
            "provider": "arcgis_poi",
        }
        return None

    geocode_cache[cache_key] = {
        "lat": best["lat"],
        "lon": best["lon"],
        "name": best["name"],
        "query": wb_text,
        "provider": "arcgis_poi",
    }
    return {
        "lat": best["lat"],
        "lon": best["lon"],
        "name": best["name"],
        "distance_km": best["distance_km"],
        "amenity": "cemetery",
    }


def find_church_poi_non_osm(location_text, geocode_cache, expected_country_codes=None):
    """Find a church POI around a city/location using ArcGIS and cache the best candidate."""
    global NON_OSM_CHURCH_POI_LOOKUP_COUNT

    if is_missing(location_text):
        return None
    # Pas de limite sur le fallback église

    query_text = canonicalize_geo_query(str(location_text).strip())
    if is_missing(query_text):
        return None

    cache_key = f"poi_church|{norm(query_text)}"
    if expected_country_codes:
        cache_key += "|cc:" + "-".join(sorted(expected_country_codes))

    cached = geocode_cache.get(cache_key)
    if isinstance(cached, dict) and "lat" in cached and "lon" in cached:
        try:
            lat = float(cached["lat"])
            lon = float(cached["lon"])
            cached_name = str(cached.get("name") or "")
            if not has_church_signal(cached_name):
                raise ValueError("cached church POI is not church-like")
            if expected_country_codes and not coords_match_expected_country(
                lat,
                lon,
                expected_country_codes,
                strict_required=True,
            ):
                raise ValueError("cached church POI country mismatch")
            return {
                "lat": lat,
                "lon": lon,
                "name": cached_name if cached_name else f"church, {query_text}",
                "distance_km": 0.0,
                "amenity": "church",
            }
        except Exception:
            pass
    if isinstance(cached, dict) and cached.get("status") == "NOT_FOUND":
        return None

    NON_OSM_CHURCH_POI_LOOKUP_COUNT += 1

    ref_lat, ref_lon = geocode_location(
        query_text,
        geocode_cache,
        expected_country_codes=expected_country_codes,
    )

    church_queries = (
        f"church, {query_text}",
        f"chiesa, {query_text}",
        f"iglesia, {query_text}",
    )

    best = None
    tokens = _build_cemetery_name_tokens(query_text)
    poi_timeout = max(5, int(GEOCODE_REQUEST_TIMEOUT_SECONDS))

    for query in church_queries:
        try:
            results = arcgis_geolocator.geocode(
                query,
                timeout=poi_timeout,
                exactly_one=False,
            )
        except Exception:
            results = None
        if not results:
            continue
        if not isinstance(results, list):
            results = [results]

        for loc in results[:8]:
            try:
                lat = float(loc.latitude)
                lon = float(loc.longitude)
            except Exception:
                continue
            if not math.isfinite(lat) or not math.isfinite(lon):
                continue
            if expected_country_codes and not coords_match_expected_country(
                lat,
                lon,
                expected_country_codes,
                strict_required=True,
            ):
                continue

            address = str(getattr(loc, "address", "") or "").strip()
            addr_norm = norm(address)
            if has_diplomatic_signal(addr_norm):
                continue
            if not has_church_signal(addr_norm):
                continue

            score = 0.0
            if has_church_signal(addr_norm):
                score += 45.0
            for tok in tokens:
                if tok in addr_norm:
                    score += 7.0

            distance_km = 0.0
            if ref_lat is not None and ref_lon is not None:
                distance_km = haversine_km(float(ref_lat), float(ref_lon), lat, lon)
                score += max(0.0, 30.0 - min(distance_km, 30.0))

            candidate = {
                "lat": lat,
                "lon": lon,
                "name": address if address else f"church, {query_text}",
                "distance_km": distance_km,
                "amenity": "church",
                "score": score,
            }
            if (
                best is None
                or candidate["score"] > best["score"]
                or (
                    candidate["score"] == best["score"]
                    and candidate["distance_km"] < best["distance_km"]
                )
            ):
                best = candidate

    if best is None:
        # Fallback Overpass OSM direct si rien trouvé
        # On tente de géocoder la ville pour obtenir lat/lon
        city_lat, city_lon = None, None
        if query_text:
            city_lat, city_lon = geocode_location(query_text, geocode_cache, expected_country_codes=expected_country_codes)
        if city_lat is not None and city_lon is not None:
            overpass_church = find_nearest_church_from_osm_overpass(city_lat, city_lon, max_distance_km=10.0)
            if overpass_church is not None:
                geocode_cache[cache_key] = {
                    "lat": overpass_church["lat"],
                    "lon": overpass_church["lon"],
                    "name": overpass_church["name"],
                    "query": query_text,
                    "provider": "overpass_church_poi",
                }
                return overpass_church
        geocode_cache[cache_key] = {
            "status": "NOT_FOUND",
            "last_try_ts": time.time(),
            "query": query_text,
            "provider": "arcgis_church_poi",
        }
        return None

    geocode_cache[cache_key] = {
        "lat": best["lat"],
        "lon": best["lon"],
        "name": best["name"],
        "query": query_text,
        "provider": "arcgis_church_poi",
    }
    return {
        "lat": best["lat"],
        "lon": best["lon"],
        "name": best["name"],
        "distance_km": best["distance_km"],
        "amenity": "church",
    }


def extract_lat_lon_from_text(*values):
    """Try to extract decimal latitude/longitude pairs from free-text fields."""
    for raw in values:
        if is_missing(raw):
            continue
        text = str(raw)
        match = re.search(r"(-?\d{1,2}(?:\.\d+)?)\s*[,;/]\s*(-?\d{1,3}(?:\.\d+)?)", text)
        if not match:
            continue
        try:
            lat = float(match.group(1))
            lon = float(match.group(2))
        except Exception:
            continue
        if -90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0:
            return lat, lon
    return None, None


def build_primary_geo_query(row):
    """Location priority: Location_of_death -> Where_found/Wheefound."""
    country = str(row.get("Country", "") or "").strip()
    city = str(row.get("City/Town/Village", "") or "").strip()
    location_of_death = str(row.get("Location_of_death", "") or "").strip()
    where_found = str(
        row.get("Where_found", "")
        or row.get("Wheefound", "")
        or row.get("Where found", "")
        or ""
    ).strip()

    sea_only_markers = {
        "sea",
        "at sea",
        "high seas",
        "mediterranean sea",
    }
    # Prefixes that signal water/vessel context → fall back to city
    sea_prefix_markers = (
        "sea",
        "high seas",
        "on board",
        "offshore",
        "overboard",
        "at sea",
    )

    for candidate in (location_of_death, where_found):
        if is_missing(candidate):
            continue
        candidate_norm = norm(candidate)
        specific_sea_place = extract_specific_sea_place(candidate)
        if specific_sea_place:
            if not is_missing(country) and norm(country) not in norm(specific_sea_place):
                return f"{specific_sea_place}, {country}"
            return specific_sea_place
        if (
            candidate_norm in sea_only_markers
            or any(candidate_norm.startswith(p) for p in sea_prefix_markers)
        ) and not is_missing(city):
            if not is_missing(country) and norm(country) not in norm(city):
                return f"{city}, {country}"
            return city
        if not is_missing(country) and norm(country) not in norm(candidate):
            return f"{candidate}, {country}"
        return candidate
    return None


def build_textual_geo_fallback(row):
    """Last-resort textual geocoding query when no dedicated location column is usable."""
    country = str(row.get("Country", "") or "").strip()
    route = str(row.get("Route", "") or row.get("Migration route", "") or "").strip()
    context_bits = []
    for col in ("Circumstances", "Details_of_incident", "Other_information"):
        value = row.get(col, "")
        if is_missing(value):
            continue
        cleaned = re.sub(r"\s+", " ", str(value)).strip()
        if cleaned:
            context_bits.append(cleaned)

    base_parts = []
    if not is_missing(route):
        base_parts.append(route)
    if context_bits:
        base_parts.append(" ".join(context_bits)[:180])
    if not is_missing(country):
        base_parts.append(country)

    if not base_parts:
        return None
    return ", ".join(base_parts)


def load_wkt_cache(path):
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


def save_wkt_cache(path, cache):
    try:
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(cache, fh, ensure_ascii=False, indent=2)
    except Exception:
        pass


def safe_build_wkt(location_label, lat, lon, geocoded_fallback):
    """Build WKT without failing on Windows cp1252 consoles."""
    if FAST_POINT_WKT_FOR_GEOCODED and bool(geocoded_fallback):
        return f"POINT({float(lon)} {float(lat)})"

    normalized_label = canonicalize_geo_query(location_label) or str(location_label)
    cache_key = f"{norm(normalized_label)}|{round(float(lat), 5)}|{round(float(lon), 5)}|{1 if geocoded_fallback else 0}"
    cached_wkt = WKT_CACHE.get(cache_key)
    if cached_wkt is not None:
        return cached_wkt

    try:
        wkt = build_wkt_for_location_precision(normalized_label, float(lat), float(lon), geocoded_fallback)
    except UnicodeEncodeError:
        wkt = f"POINT({float(lon)} {float(lat)})"

    WKT_CACHE[cache_key] = wkt
    return wkt


def _build_cemetery_name_tokens(raw_text):
    if is_missing(raw_text):
        return []
    text = norm(raw_text)
    words = re.findall(r"[a-z0-9]+", text)
    stopwords = {
        "cemetery", "graveyard", "grave", "yard", "burial", "ground",
        "cimetiere", "cimitero", "cementerio", "de", "du", "des", "del",
        "della", "di", "la", "le", "les", "the", "and", "et", "in",
    }
    tokens = [w for w in words if len(w) >= 3 and w not in stopwords]
    return tokens


def _score_cemetery_name_match(cemetery_name, where_buried_hint):
    if is_missing(cemetery_name) or is_missing(where_buried_hint):
        return 0

    name_norm = norm(cemetery_name)
    hint_norm = norm(where_buried_hint)
    if not name_norm or not hint_norm:
        return 0

    # Exact or near-exact textual overlap gets highest priority.
    if name_norm in hint_norm or hint_norm in name_norm:
        return 1000

    tokens = _build_cemetery_name_tokens(where_buried_hint)
    if not tokens:
        return 0

    matches = sum(1 for tok in tokens if tok in name_norm)
    return matches


def find_nearest_cemetery_from_death_location(death_lat, death_lon, max_distance_km, min_distance_km=0.0, where_buried_hint=None, force_lookup=False):
    """Return nearest OSM cemetery-like amenity around death coordinates.

    Uses Overpass with strict amenity filter (grave_yard|cemetery) and returns
    a dict with lat/lon/name/distance when a nearby cemetery exists.
    """
    try:
        death_lat = float(death_lat)
        death_lon = float(death_lon)
    except Exception:
        return None

    if not USE_OVERPASS_CEMETERY_PROVIDER and not force_lookup:
        return None

    if not math.isfinite(death_lat) or not math.isfinite(death_lon):
        return None

    radius_m = int(max(1.0, float(max_distance_km)) * 1000.0)
    overpass_query = (
        "[out:json][timeout:25];"
        "("
        f"node[\"amenity\"~\"^(grave_yard|cemetery)$\"](around:{radius_m},{death_lat},{death_lon});"
        f"way[\"amenity\"~\"^(grave_yard|cemetery)$\"](around:{radius_m},{death_lat},{death_lon});"
        f"relation[\"amenity\"~\"^(grave_yard|cemetery)$\"](around:{radius_m},{death_lat},{death_lon});"
        f"node[\"landuse\"=\"cemetery\"](around:{radius_m},{death_lat},{death_lon});"
        f"way[\"landuse\"=\"cemetery\"](around:{radius_m},{death_lat},{death_lon});"
        f"relation[\"landuse\"=\"cemetery\"](around:{radius_m},{death_lat},{death_lon});"
        ");"
        "out center tags;"
    )

    global OVERPASS_CONSECUTIVE_FAILURES, OVERPASS_DISABLED_UNTIL_TS, FORCED_OVERPASS_CEMETERY_LOOKUP_COUNT

    if (
        force_lookup
        and MAX_FORCED_OVERPASS_CEMETERY_PER_RUN is not None
        and FORCED_OVERPASS_CEMETERY_LOOKUP_COUNT >= int(MAX_FORCED_OVERPASS_CEMETERY_PER_RUN)
    ):
        return None
    if force_lookup:
        FORCED_OVERPASS_CEMETERY_LOOKUP_COUNT += 1

    now_ts = time.time()
    if OVERPASS_DISABLED_UNTIL_TS and now_ts < OVERPASS_DISABLED_UNTIL_TS:
        return None

    data = urllib.parse.urlencode({"data": overpass_query}).encode("utf-8")
    parsed = None
    overpass_endpoints = (
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.fr/api/interpreter",
    )

    for endpoint in overpass_endpoints:
        req = urllib.request.Request(
            endpoint,
            data=data,
            headers={
                "User-Agent": "frontlet_southern_eu_cemetery_locator/1.0",
                "Accept": "application/json",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=OVERPASS_REQUEST_TIMEOUT_SECONDS) as resp:
                payload = resp.read().decode("utf-8", errors="replace")
            parsed = json.loads(payload)
            OVERPASS_CONSECUTIVE_FAILURES = 0
            OVERPASS_DISABLED_UNTIL_TS = 0.0
            break
        except Exception:
            continue

    if parsed is None:
        OVERPASS_CONSECUTIVE_FAILURES += 1
        if OVERPASS_CONSECUTIVE_FAILURES >= 2:
            OVERPASS_DISABLED_UNTIL_TS = time.time() + float(OVERPASS_FAILURE_COOLDOWN_SECONDS)
        return None

    elements = parsed.get("elements", []) if isinstance(parsed, dict) else []
    best = None
    best_matching_name = None

    for elem in elements:
        if not isinstance(elem, dict):
            continue
        lat = elem.get("lat")
        lon = elem.get("lon")
        if lat is None or lon is None:
            center = elem.get("center") if isinstance(elem.get("center"), dict) else None
            if center is not None:
                lat = center.get("lat")
                lon = center.get("lon")
        try:
            cand_lat = float(lat)
            cand_lon = float(lon)
        except Exception:
            continue
        if not math.isfinite(cand_lat) or not math.isfinite(cand_lon):
            continue

        distance_km = haversine_km(death_lat, death_lon, cand_lat, cand_lon)
        if distance_km < float(min_distance_km) or distance_km > float(max_distance_km):
            continue

        tags = elem.get("tags") if isinstance(elem.get("tags"), dict) else {}
        amenity = str(tags.get("amenity", "")).strip().lower()
        landuse = str(tags.get("landuse", "")).strip().lower()
        if amenity not in {"grave_yard", "cemetery"} and landuse != "cemetery":
            continue

        name = str(tags.get("name", "")).strip()
        name_match_score = _score_cemetery_name_match(name, where_buried_hint)
        candidate = {
            "lat": cand_lat,
            "lon": cand_lon,
            "distance_km": distance_km,
            "name": name if name else "cemetery",
            "amenity": amenity or landuse or "cemetery",
            "name_match_score": name_match_score,
        }

        if name_match_score > 0:
            if (
                best_matching_name is None
                or candidate["name_match_score"] > best_matching_name["name_match_score"]
                or (
                    candidate["name_match_score"] == best_matching_name["name_match_score"]
                    and candidate["distance_km"] < best_matching_name["distance_km"]
                )
            ):
                best_matching_name = candidate

        if best is None or candidate["distance_km"] < best["distance_km"]:
            best = candidate

    return best_matching_name or best


# --------------------- Pays ---------------------------
def ensure_country_node(g, country_code_or_name, prefix="southern_eu"):
    global COUNTRY_NAME_INDEX

    if is_missing(country_code_or_name):
        return None

    cache_key = (prefix, norm(country_code_or_name))
    cached_uri = COUNTRY_NODE_CACHE.get(cache_key)
    if cached_uri is not None:
        return cached_uri

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
        if COUNTRY_NAME_INDEX is None:
            COUNTRY_NAME_INDEX = _build_country_name_index()
        cc = COUNTRY_NAME_INDEX.get(norm(val))

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
        COUNTRY_NODE_CACHE[cache_key] = uri
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
    COUNTRY_NODE_CACHE[cache_key] = uri
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
    age_uri = DATA[f"southern_eu_Age_{node_suffix}"]
    g.add((age_uri, RDF.type, F.Age))
    g.add((age_uri, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    g.add((age_uri, RDFS.label, Literal(f"{age_num} years old", lang="en")))
    return age_uri


def create_age_interval_node(g, age_value, node_suffix):
    """Ressource frontlet:AgeInterval nommée pour un âge estimé / une fourchette."""
    if is_missing(age_value):
        return None
    label = str(age_value).strip()
    age_uri = DATA[f"southern_eu_AgeInterval_{node_suffix}"]
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
        src_col = columns_by_norm.get("southern_eu") or columns_by_norm.get("ue_sud")
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
MISSING_KEYWORDS = (
    "disparu",
    "disparue",
    "disparus",
    "disparues",
    "disparition",
    "missing",
    "not found",
    "body not found",
    "never found",
    "unaccounted",
)
CEMETERY_KEYWORDS = (
    "cemet",
    "cimeti",
    "graveyard",
    "grave yard",
    "burial ground",
    "cimiter",
    "cementer",
)
INHUMATION_MIN_DISTANCE_KM = 0.05
INHUMATION_MAX_DISTANCE_KM = 20.0
INHUMATION_SAME_CITY_MAX_DISTANCE_KM = 12.0


def contains_any_keyword(value, keywords):
    text = norm(value)
    return bool(text) and any(keyword in text for keyword in keywords)


def haversine_km(lat1, lon1, lat2, lon2):
    """Great-circle distance in kilometers between two WGS84 points."""
    r = 6371.0088
    phi1 = math.radians(float(lat1))
    phi2 = math.radians(float(lat2))
    d_phi = math.radians(float(lat2) - float(lat1))
    d_lam = math.radians(float(lon2) - float(lon1))
    a = math.sin(d_phi / 2.0) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(d_lam / 2.0) ** 2
    return 2.0 * r * math.asin(math.sqrt(a))


def build_tagged_comment(row, columns):
    parts = []
    for column in columns:
        value = row.get(column, "")
        if not is_missing(value):
            parts.append(f"{column}: {str(value).strip()}")
    return "; ".join(parts)


def extract_first_url(*values):
    """Extract first HTTP/HTTPS URL found in free-text values."""
    url_pattern = re.compile(r"https?://[^\s\]\[\)\(\"'<>;]+", re.IGNORECASE)
    for raw in values:
        if is_missing(raw):
            continue
        match = url_pattern.search(str(raw))
        if match:
            return match.group(0).strip()
    return None


def build_event_context_narrative(row):
    """Build concise narrative context from incident/circumstances fields."""
    parts = []
    for col in ("Details_of_incident", "Circumstances", "Other_information"):
        value = row.get(col, "")
        if is_missing(value):
            continue
        cleaned = re.sub(r"\s+", " ", str(value)).strip()
        if cleaned:
            parts.append(cleaned)
    return " ; ".join(parts) if parts else None


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
DISAPPEARANCE_EVENT_CLASS = find_by_label(g_ref, "Disappearance") or F.Disappearance
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
PROP_hasWebLink     = find_by_label(g_ref, "has web link") or F.hasWebLink
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

# Instances frontlet:Gender (comme IOM)

# Chargement du DataFrame principal
df = pd.read_csv(CSV_PATH, encoding="latin1", sep=';')
if ROW_LIMIT is not None:
    df = df.head(ROW_LIMIT)
count_person = 0
count_missing_inferred = 0

count_disappearance_events = 0
count_control_events = 0
count_inhumation = 0
count_repatriation = 0
count_additional_typed_events = 0
count_cause_matched = 0
count_cause_literal = 0
count_death_nature = 0
count_geocode_success = 0
count_geocode_failed = 0
count_geom_propagated = 0
count_event_country_from_geometry = 0

created_collective_events = {}
geocode_cache = load_geocode_cache(GEOCODE_CACHE_PATH)
WKT_CACHE = load_wkt_cache(WKT_CACHE_PATH)

for idx, row in df.iterrows():
    row_num = idx + 1
    person_uri = DATA[f"southern_eu_Person_{row_num}"]
    g.add((person_uri, RDF.type, PERSON_CLASS))

    # Recherche du lieu d'inhumation (cimetière ou église uniquement, PAS de fallback pays/ville)
    where_buried = row.get("Where buried", "")
    country_val = row.get("Country", "")
    city_val = row.get("City/Town/Village", "")
    wb_country_codes = resolve_expected_country_codes(country_val)

    burial_point = None
    # 1. Cimetière (ArcGIS/OSM)
    if not is_missing(where_buried):
        burial_point = find_cemetery_poi_non_osm(where_buried, geocode_cache, expected_country_codes=wb_country_codes, force_lookup=True)
    # 2. Si pas de cimetière, tenter église (ArcGIS/OSM)
    if burial_point is None and not is_missing(city_val):
        burial_point = find_church_poi_non_osm(city_val, geocode_cache, expected_country_codes=wb_country_codes)

    # Si trouvé, écrire la géométrie sur le TTL
    if burial_point is not None:
        inhumation_uri = DATA[f"InhumationEvent_{row_num}"]
        g.add((inhumation_uri, RDF.type, INHUMATION_EVENT_CLASS))
        g.add((person_uri, PROP_composedOf, inhumation_uri))
        inhumation_lat = float(burial_point["lat"])
        inhumation_lon = float(burial_point["lon"])
        amenity = burial_point.get("amenity", "cemetery")
        label_base = str(burial_point.get("name") or amenity).strip()
        burial_label = f"Cemetery: {label_base}" if amenity == "cemetery" else f"Church: {label_base}"
        wkt_inh = safe_build_wkt(burial_label, inhumation_lat, inhumation_lon, True)
        geom_inh_uri = DATA[f"southern_eu_geometry_inhumation_{row_num}"]
        g.add((inhumation_uri, GEO.hasGeometry, geom_inh_uri))
        g.add((geom_inh_uri, RDF.type, GEO.Geometry))
        g.add((geom_inh_uri, GEO.asWKT, Literal(wkt_inh, datatype=GEO.wktLiteral)))
        g.add((geom_inh_uri, F.hasPrecision, Literal(False, datatype=XSD.boolean)))
        g.add((inhumation_uri, F.lieu, Literal(burial_label)))
    # Sinon, ne rien écrire (pas de fallback pays/ville)
        # ...existing code...
print(f"Control events created      : {count_control_events}")
print(f"Inhumation events created   : {count_inhumation}")
print(f"Repatriation events created : {count_repatriation}")
print(f"Other typed events created  : {count_additional_typed_events}")
print(f"Disappearance events created: {count_disappearance_events}")
print()
print("Cause décès - mapping thesaurus :")
print(f"  - Matched to thesaurus URI : {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"  - DeathNature linked : {count_death_nature}")
print()
print("Géocodage :")
print(f"  - Réussis   : {count_geocode_success}")
print(f"  - Non résolus: {count_geocode_failed}")
print(f"  - Nominatim rate limit : {'oui' if NOMINATIM_RATE_LIMITED else 'non'}")
print(f"  - Disparitions inférées (texte): {count_missing_inferred}")
print(f"Geometry propagated to siblings: {count_geom_propagated}")
print(f"Event countries from geometry: {count_event_country_from_geometry}")
print("=" * 60)
print(f"Output written to: {OUTPUT_TTL}")


