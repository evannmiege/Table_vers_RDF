#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV espagne_frontera_sur → ontologie RDF selon vos règles.
Amélioration du mapping Cause_deces avec le thésaurus DeathCause (prefLabel@fr)
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
from geopy.geocoders import Nominatim, Photon
from geopy.exc import GeocoderTimedOut, GeocoderServiceError, GeocoderRateLimited
import time
from event_text_utils import (
    _throttle_boundary_lookup,
    add_additional_typed_events,
    add_event_country_from_geometry,
    build_additional_event_specs,
    build_cemetery_geocode_cache,
    build_wkt_for_location_precision,
    collect_text_values_from_row,
    force_local_area_wkt_from_point,
    infer_day_of_week_name,
    infer_source_category_key,
    load_boundary_wkt_cache,
    propagate_geometry_to_sibling_events,
    save_boundary_wkt_cache,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
CSV_PATH = "espagne_frontera_sur/espagne_frontera_sur.csv"
OUTPUT_TTL = "espagne_frontera_sur/frontlet_import_output.ttl"
MAPPING_PATH = "espagne_frontera_sur/mappingEspagneFronteraSurThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)
GEOCODE_CACHE_PATH = "espagne_frontera_sur/geocode_cache.json"
BOUNDARY_CACHE_PATH = "espagne_frontera_sur/boundary_wkt_cache.json"
GEOCODE_TIME_BUDGET_SEC = 25
GEOCODE_MAX_AFTER_BUDGET = 8
GEOCODER_MIN_DELAY_SECONDS = 0.35
GEOCODER_MAX_ATTEMPTS = 3
DISABLE_LIVE_GEOCODING = True
# For geocoded imprecise locations, prefer real boundary polygons (fallback: non-square local polygon).
USE_BOUNDARY_WKT_FOR_GEOCODED = True

# Bounding boxes par ZONA : (lat_min, lat_max, lon_min, lon_max)
# Utilisé pour valider que le lieu géocodé depuis LUGAR est bien dans la bonne zone géographique.
_ZONA_BOUNDING_BOXES = {
    "marruecos":   (27.0, 36.0, -14.0, -1.0),
    "maroc":       (27.0, 36.0, -14.0, -1.0),
    "canarias":    (27.0, 30.0, -19.0, -13.0),
    "almeria":     (36.5, 37.5, -3.5, -1.3),
    "almería":     (36.5, 37.5, -3.5, -1.3),
    "ceuta":       (35.7, 36.0, -5.5, -5.1),
    "cabo verde":  (14.5, 17.5, -25.5, -22.0),
    "argelia":     (18.0, 37.5, -9.0, 12.0),
    "sahara":      (20.0, 28.0, -18.0, 0.0),
    "melilla":     (35.2, 35.4, -3.1, -2.8),
    "levante":     (37.0, 41.5, -2.0, 1.5),
    "senegal":     (12.0, 16.5, -18.0, -11.0),
    "nador":       (34.8, 35.4, -3.2, -2.5),
    "cadiz":       (35.8, 37.5, -6.5, -4.8),
    "cádiz":       (35.8, 37.5, -6.5, -4.8),
    "malaga":      (36.0, 37.5, -5.2, -3.5),
    "málaga":      (36.0, 37.5, -5.2, -3.5),
    "baleares":    (38.5, 40.2, 1.0, 4.5),
    "mauritania":  (14.0, 28.0, -18.0, -4.5),
    "granada":     (36.5, 38.0, -4.5, -2.5),
}

ZONA_BBOX_MARGIN = 0.8  # degrés de tolérance autour de la bounding box ZONA
GLOBAL_FALLBACK_BBOX = (10.0, 44.0, -25.5, 15.0)  # emprise dataset (Europe du sud / Maghreb / Atlantique Est)
MAX_BBOX_POLYGON_AREA_DEG2 = 30.0  # au-dela, fallback en POINT pour eviter les mega-polygones
# Traduction espagnol → anglais pour les noms de pays dans LUGAR (ex: "Argelia-Orán" → "Oran, Algeria")
_ES_COUNTRY_TO_EN = {
    "argelia": "Algeria",
    "marruecos": "Morocco",
    "maroc": "Morocco",
    "senegal": "Senegal",
    "mauritania": "Mauritania",
    "cabo verde": "Cape Verde",
    "espana": "Spain",
    "españa": "Spain",
    "ceuta": "Ceuta, Spain",
    "melilla": "Melilla, Spain",
    "canarias": "Canary Islands, Spain",
    "baleares": "Balearic Islands, Spain",
}

def _preprocess_lugar_for_geocoding(lugar_text, country_hint=None):
    """Prétraite un texte LUGAR pour le géocodage :
    - Traduit les noms de pays espagnols en anglais
    - Divise les composés type 'Argelia-Orán' en (lieu='Orán', hint='Algeria')
    Retourne une liste de (texte_geocodage, hint) à essayer.
    """
    if not lugar_text:
        return [(lugar_text, country_hint)]

    results = []
    txt = lugar_text.strip()
    txt_norm = norm(txt)

    # Traduction directe des libellés de zone (ex: Baleares -> Balearic Islands, Spain)
    direct_en = _ES_COUNTRY_TO_EN.get(txt_norm)
    if direct_en:
        results.append((direct_en, None))

    # Détecter si le LUGAR contient "NomPays-NomVille" ou "NomPays - NomVille"
    for es_country, en_country in _ES_COUNTRY_TO_EN.items():
        pattern = re.compile(
            r"^" + re.escape(es_country) + r"\s*[-–]\s*(.+)$", re.IGNORECASE
        )
        m = pattern.match(txt)
        if m:
            city_part = m.group(1).strip()
            if city_part and len(city_part) >= 2:
                # Priorité: ville + pays anglais
                results.append((city_part + ", " + en_country, None))
                results.append((city_part, en_country))
            break
        # Aussi: "NomVille en NomPays" → city_part avec hint pays
        pattern2 = re.compile(
            r"^(.+?)\s+en\s+" + re.escape(es_country) + r"$", re.IGNORECASE
        )
        m2 = pattern2.match(txt)
        if m2:
            city_part = m2.group(1).strip()
            if city_part and len(city_part) >= 2:
                results.append((city_part + ", " + en_country, None))
                results.append((city_part, en_country))
            break

    # Fallback : garder le texte original avec son hint
    results.append((txt, country_hint))
    # Dédupliquer tout en gardant l'ordre
    seen = set()
    out = []
    for t, h in results:
        k = norm(t)
        if k and k not in seen:
            seen.add(k)
            out.append((t, h))
    return out

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


def bbox_to_wkt_polygon(lat_min, lat_max, lon_min, lon_max):
    """Construit un POLYGON WKT axis-aligned a partir d'une bbox."""
    return (
        f"POLYGON(({lon_min} {lat_min}, {lon_max} {lat_min}, "
        f"{lon_max} {lat_max}, {lon_min} {lat_max}, {lon_min} {lat_min}))"
    )

# Labels explicitement bloqués pour éviter l'entité contestée "république sahraouie"
_TOO_VAGUE_FOR_GEOCODING = {
    "western sahara", "sahrawi arab democratic republic", "republique sahraouie", "republique sahraoui",
}

_NON_PLACE_HINT_TOKENS = {
    "muerte", "desaparicion", "desaparecido", "patera", "embarcacion", "travesia",
    "interceptacion", "naufragio", "persona", "personas", "vida", "cadaver",
    "hombre", "mujer", "joven", "chico", "madre", "nina", "nino", "pone",
    "chepot", "bordo", "ruta", "aparicion", "aparece", "hallan", "encuentran",
    "durante", "fallecida", "fallecido", "pierna", "cayuco", "aguas",
    # Adjectifs de nationalité et fragments narratifs fréquents dans NOTA
    "marroqui", "subsahariano", "subsahariana", "yemeni", "gambiano",
    "nigeriano", "maliense", "senegalese", "senegalesa", "argelino", "argelina",
    "llamado", "llamada", "conakri", "morgue", "procedente", "asociacion",
    "cruzar", "traves", "atraves",
}

_PLACE_CONNECTOR_TOKENS = {
    "de", "del", "la", "las", "el", "los", "y", "en", "al", "a"
}

_GENERIC_LOCATION_TOKENS = {
    "playa", "costa", "costa", "zona", "mar", "oceano", "océano", "agua", "aguas",
    "puerto", "frontera", "ruta", "lugar", "sitio"
}

_MACRO_LOCATION_LABELS = {
    "canarias", "islas canarias", "canary islands",
    "mauritania", "marruecos", "maroc", "argelia", "algeria", "algerie", "algérie",
    "cabo verde", "cape verde", "sahara", "western sahara", "sahara occidental",
    "espana", "españa", "spain",
    "senegal", "atlantico", "atlántico", "mediterraneo", "mediterráneo",
}

def is_too_vague_for_geocoding(location_str):
    """Retourne True pour labels contestés ou fragments textuels non topographiques."""
    if not location_str:
        return True
    normalized = norm(location_str)
    if normalized in _TOO_VAGUE_FOR_GEOCODING:
        return True

    # Écarter les fragments textuels de NOTA qui ne sont pas des toponymes.
    words = [w for w in re.findall(r"[a-z]+", normalized) if len(w) > 1]
    if not words:
        return True
    if words[0].startswith("aparic") or words[0].startswith("desaparec") or words[0].startswith("durante"):
        return True
    if any(w in _NON_PLACE_HINT_TOKENS for w in words):
        return True
    meaningful = [w for w in words if w not in _PLACE_CONNECTOR_TOKENS]
    if not meaningful:
        return True
    if all(w in _GENERIC_LOCATION_TOKENS for w in meaningful):
        return True
    return False


def is_macro_location_label(location_str):
    """Retourne True si le libellé ressemble à une zone trop large (pays/région/mer)."""
    if not location_str:
        return True
    txt = norm(location_str)
    txt = re.sub(r"[()\[\],;:.]", " ", txt)
    txt = re.sub(r"\s+", " ", txt).strip()
    if txt in _MACRO_LOCATION_LABELS:
        return True
    # Exemples typiques: "ruta de canarias", "costas de mauritania"
    if re.search(r"\b(ruta|costas?|aguas|frontera|oceano|oc[eé]ano|mar)\b", txt):
        return True
    return False


def should_use_local_boundary_polygon(location_str):
    """Retourne True pour des micro-toponymes (plage/quartier/etc.) adaptés à un contour local."""
    if not location_str:
        return False
    txt = norm(location_str)
    if not txt or is_too_vague_for_geocoding(location_str) or is_macro_location_label(location_str):
        return False

    # Signaux de lieux fins (ex: Playa de la Ribera, El Sarchal, Punta ...)
    local_markers = (
        "playa", "beach", "sarchal", "ribera", "punta", "cala", "bahia", "bahía",
        "barrio", "quartier", "muelle", "puerto", "cabo", "ensenada", "higuericas",
        "hornillo", "desnarigado", "embarcadero"
    )
    if any(m in txt for m in local_markers):
        return True

    # Lieux composés avec au moins deux mots significatifs.
    words = [w for w in re.findall(r"[a-záéíóúñü]+", txt) if len(w) > 1 and w not in _PLACE_CONNECTOR_TOKENS]
    return len(words) >= 3


def _is_polygon_wkt(wkt_value):
    txt = str(wkt_value or "").strip().upper()
    return txt.startswith("POLYGON((")


def _is_axis_aligned_bbox_polygon_wkt(wkt_value):
    """Return True for square/rectangle polygons that are simple bbox-like shells."""
    txt = str(wkt_value or "").strip()
    m = re.match(r"^POLYGON\s*\(\((.+)\)\)$", txt, flags=re.IGNORECASE)
    if not m:
        return False
    try:
        coords = []
        for part in m.group(1).split(","):
            bits = re.split(r"\s+", part.strip())
            if len(bits) < 2:
                return False
            x = float(bits[0])
            y = float(bits[1])
            coords.append((x, y))
        if len(coords) < 5:
            return False
        # Remove duplicated closing vertex for topology checks.
        if coords[0] == coords[-1]:
            core = coords[:-1]
        else:
            core = coords
        if len(core) != 4:
            return False
        unique_x = {c[0] for c in core}
        unique_y = {c[1] for c in core}
        # A pure bbox shell has exactly 2 unique longitudes and 2 unique latitudes.
        return len(unique_x) == 2 and len(unique_y) == 2
    except Exception:
        return False


def _coerce_event_wkt(location_label, wkt_value, lat_value, lon_value):
    """Keep only local contour polygons; fallback to point otherwise."""
    if not _is_polygon_wkt(wkt_value):
        return wkt_value

    if not should_use_local_boundary_polygon(location_label):
        return f"POINT({float(lon_value)} {float(lat_value)})"

    if _is_axis_aligned_bbox_polygon_wkt(wkt_value):
        return f"POINT({float(lon_value)} {float(lat_value)})"

    return wkt_value


def _is_macro_fallback_label(label_text):
    if is_missing(label_text):
        return True
    return is_macro_location_label(label_text)


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

# Initialiser le géocodeur Photon avec cache JSON persistant
geolocator = Photon(user_agent="frontlet_espagne_geocoder")
cemetery_geolocator = Nominatim(user_agent="frontlet_espagne_cemetery_geocoder")
country_geolocator = Nominatim(user_agent="frontlet_espagne_country_geocoder")
_last_geocode_ts = 0.0

if os.path.exists(GEOCODE_CACHE_PATH):
    try:
        with open(GEOCODE_CACHE_PATH, encoding="utf-8") as _f:
            location_geocode_cache = json.load(_f)
    except Exception:
        location_geocode_cache = {}
else:
    location_geocode_cache = {}

# Charger le cache boundary WKT (polygones OSM) depuis le disque pour éviter les re-fetch.
load_boundary_wkt_cache(BOUNDARY_CACHE_PATH)

# Eviter de recycler d'anciens géocodages ambigus pour les libellés "Marruecos".
for _k in list(location_geocode_cache.keys()):
    if "marruecos" in str(_k).lower() or "morocco" in str(_k).lower():
        location_geocode_cache.pop(_k, None)

geocoding_calls_count = 0
geocoding_cache_hits = 0
geocoding_skipped_budget = 0
geocoding_start_time = time.time()
geocoding_after_budget_calls = 0
_reverse_country_cache = {}


def _save_geocode_cache():
    try:
        os.makedirs(os.path.dirname(GEOCODE_CACHE_PATH), exist_ok=True)
        with open(GEOCODE_CACHE_PATH, "w", encoding="utf-8") as _f:
            json.dump(location_geocode_cache, _f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def geocode_location(location_name, region_hint=None, zona_bbox=None):
    """Géocode un nom de lieu avec Photon + cache persistant.
    Si region_hint est fourni, essaie d'abord 'location_name, region_hint' pour disambiguer.
    """
    global geocoding_calls_count, geocoding_cache_hits, geocoding_after_budget_calls
    global geocoding_skipped_budget, _last_geocode_ts

    if is_missing(location_name):
        return None, None

    location_str = str(location_name).strip()
    hint_str = str(region_hint).strip() if region_hint and not is_missing(region_hint) else None

    # Clé de cache : inclure le hint si présent pour éviter de réutiliser un résultat ambigu
    bbox_key = None
    if zona_bbox is not None:
        try:
            bbox_key = "{:.2f},{:.2f},{:.2f},{:.2f}".format(
                float(zona_bbox[0]), float(zona_bbox[1]), float(zona_bbox[2]), float(zona_bbox[3])
            )
        except Exception:
            bbox_key = None

    if hint_str and norm(hint_str) != norm(location_str):
        cache_key = norm(location_str) + " | " + norm(hint_str)
        queries = [f"{location_str}, {hint_str}", location_str]
    else:
        cache_key = norm(location_str)
        queries = [location_str]
    if bbox_key:
        cache_key = cache_key + " | bbox=" + bbox_key

    # Désambiguïsation explicite pour les lieux contenant Marruecos/Morocco.
    is_morocco_label = bool(re.search(r"\b(marruecos|morocco|maroc)\b", norm(location_str)))
    if is_morocco_label:
        parts = [p.strip() for p in re.split(r"[-,]", location_str) if p and p.strip()]
        local_part = parts[0] if parts else location_str
        prioritized = []
        if local_part:
            prioritized.append(f"{local_part}, Morocco")
            prioritized.append(f"{local_part}, Maroc")
        prioritized.append(f"{location_str}, Morocco")
        prioritized.append(f"{location_str}, Maroc")
        for q in queries:
            if q not in prioritized:
                prioritized.append(q)
        queries = prioritized

    if cache_key in location_geocode_cache:
        cached = location_geocode_cache[cache_key]
        geocoding_cache_hits += 1
        return (cached[0], cached[1]) if cached else (None, None)

    # Mode sans réseau: uniquement cache local puis fallbacks géométriques du pipeline.
    if DISABLE_LIVE_GEOCODING:
        location_geocode_cache[cache_key] = None
        return None, None

    elapsed = time.time() - geocoding_start_time
    if elapsed > GEOCODE_TIME_BUDGET_SEC and geocoding_after_budget_calls >= GEOCODE_MAX_AFTER_BUDGET:
        geocoding_skipped_budget += 1
        location_geocode_cache[cache_key] = None
        return None, None
    if elapsed > GEOCODE_TIME_BUDGET_SEC:
        geocoding_after_budget_calls += 1

    def _is_plausible_morocco_coord(lat_v, lon_v):
        # Validation par pays retourné en reverse-geocoding.
        # Accepte Maroc et Sahara occidental (zones attendues dans ce dataset).
        try:
            key = (round(float(lat_v), 4), round(float(lon_v), 4))
        except Exception:
            return False
        if key in _reverse_country_cache:
            return _reverse_country_cache[key]
        ok = False
        try:
            _throttle_boundary_lookup()
            rev = country_geolocator.reverse((float(lat_v), float(lon_v)), timeout=10, language="en")
            geocoding_calls_count += 1
            if rev is not None:
                addr = getattr(rev, "raw", {}).get("address", {}) if getattr(rev, "raw", None) else {}
                country_txt = str(addr.get("country", "")).strip().lower()
                if country_txt in ("morocco", "maroc", "western sahara"):
                    ok = True
        except Exception:
            ok = False
        _reverse_country_cache[key] = ok
        return ok

    def _in_requested_bbox(lat_v, lon_v):
        if zona_bbox is None:
            return True
        try:
            lat_min, lat_max, lon_min, lon_max = [float(x) for x in zona_bbox]
            return lat_min <= float(lat_v) <= lat_max and lon_min <= float(lon_v) <= lon_max
        except Exception:
            return True

    for query in queries:
        # Pour les libellés marocains, on privilégie Nominatim pour un meilleur contexte admin.
        if is_morocco_label:
            try:
                _throttle_boundary_lookup()
                nloc = country_geolocator.geocode(query, timeout=10)
                geocoding_calls_count += 1
                if nloc:
                    lat_n = float(nloc.latitude)
                    lon_n = float(nloc.longitude)
                    if is_morocco_label and not _is_plausible_morocco_coord(lat_n, lon_n):
                        continue
                    if not _in_requested_bbox(lat_n, lon_n):
                        continue
                    is_susp_n, reason_n = is_suspicious_coordinate(lat_n, lon_n)
                    if not is_susp_n:
                        location_geocode_cache[cache_key] = [lat_n, lon_n]
                        return lat_n, lon_n
                    else:
                        print(f"  ⚠️  Coordonnée suspecte ignorée ({reason_n}): {lon_n}, {lat_n} pour '{query}'")
            except Exception:
                pass

        for attempt in range(GEOCODER_MAX_ATTEMPTS):
            wait = GEOCODER_MIN_DELAY_SECONDS - (time.time() - _last_geocode_ts)
            if wait > 0:
                time.sleep(wait)
            try:
                _last_geocode_ts = time.time()
                location = geolocator.geocode(query, timeout=10)
                geocoding_calls_count += 1
                if location:
                    lat = float(location.latitude)
                    lon = float(location.longitude)
                    if is_morocco_label and not _is_plausible_morocco_coord(lat, lon):
                        continue
                    if not _in_requested_bbox(lat, lon):
                        continue
                    is_susp, reason = is_suspicious_coordinate(lat, lon)
                    if not is_susp:
                        location_geocode_cache[cache_key] = [lat, lon]
                        return lat, lon
                    else:
                        print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon}, {lat} pour '{query}'")
                break  # Pas de résultat → essayer la query suivante
            except GeocoderRateLimited:
                time.sleep(GEOCODER_MIN_DELAY_SECONDS * (2 ** attempt))
            except (GeocoderTimedOut, GeocoderServiceError):
                continue
            except Exception:
                break

    location_geocode_cache[cache_key] = None
    return None, None


def geocode_cemetery_location(location_name, region_hint=None):
    """Try to geocode a cemetery first, then fallback to regular geocoding."""
    if is_missing(location_name):
        return None, None

    base = str(location_name).strip()
    hint = str(region_hint).strip() if region_hint and not is_missing(region_hint) else None
    if is_too_vague_for_geocoding(base):
        return None, None

    cemetery_queries = []
    if hint and norm(hint) != norm(base):
        cemetery_queries.append(f"cemetery {base}, {hint}")
    cemetery_queries.append(f"cemetery {base}")

    for query in cemetery_queries:
        try:
            results = cemetery_geolocator.geocode(query, exactly_one=False, limit=5, timeout=10)
            if results:
                matches = []
                for res in results:
                    address = str(getattr(res, "address", "")).lower()
                    if "cemetery" in address or "cimetiere" in address or "cementerio" in address:
                        matches.append(res)
                if len(matches) == 1:
                    lat = float(matches[0].latitude)
                    lon = float(matches[0].longitude)
                    is_susp, _ = is_suspicious_coordinate(lat, lon)
                    if not is_susp:
                        return lat, lon
        except Exception:
            continue

    return geocode_location(base, region_hint=hint)


def extract_location_from_nota(nota_text):
    """
    Extrait les noms de lieux depuis le texte espagnol de NOTA.
    Retourne une liste de chaînes candidates pour le géocodage (du plus précis au moins précis).
    """
    if is_missing(nota_text):
        return []
    text = str(nota_text).strip()
    candidates = []

    def _clean_candidate(raw):
        if is_missing(raw):
            return None
        val = str(raw).strip(" .,:;()[]{}\t\n\r")
        val = re.sub(r"\s+", " ", val).strip()
        if len(val) < 3:
            return None
        tokens = [t for t in re.findall(r"[a-záéíóúñü]+", norm(val)) if len(t) > 1]
        if not tokens:
            return None
        meaningful = [t for t in tokens if t not in _PLACE_CONNECTOR_TOKENS]
        if not meaningful:
            return None
        # Rejeter les fragments narratifs sans toponyme identifiable.
        if any(t in _NON_PLACE_HINT_TOKENS for t in meaningful):
            return None
        return val

    # Patterns espagnols pour extraire les lieux
    patterns = [
        r'(?:playa|plage|playa de)(?: la| del| de)? ([A-ZÁÉÍÓÚÑ][a-záéíóúñü -]+)',
        r'(?:costas? de)(?: la| las| el| los)? ([A-ZÁÉÍÓÚÑ][a-záéíóúñü -]+)',
        r'(?:puerto|muelle|canal|estrecho)(?: de)(?: la| el)? ([A-ZÁÉÍÓÚÑ][a-záéíóúñü -]+)',
        r'(?:frontera de|frontera con) ([A-ZÁÉÍÓÚÑ][a-záéíóúñü -]+)',
        r'(?:provincia de|ciudad de|municipio de) ([A-ZÁÉÍÓÚÑ][a-záéíóúñü -]+)',
        r'(?:en|hacia|cerca de|a) ([A-ZÁÉÍÓÚÑ][a-záéíóúñü]{3,}(?:\s+[A-ZÁÉÍÓÚÑ][a-záéíóúñü]+)?)',
    ]
    for pat in patterns:
        for m in re.finditer(pat, text, re.IGNORECASE):
            loc = _clean_candidate(m.group(1))
            if loc:
                candidates.append(loc)

    # Cas fréquents: "playa de la Ribera", "playa de El Sarchal".
    for m in re.finditer(r'(playa\s+de\s+(?:la|el|los|las)\s+[A-ZÁÉÍÓÚÑ][a-záéíóúñü-]+(?:\s+[A-ZÁÉÍÓÚÑ][a-záéíóúñü-]+)*)', text, re.IGNORECASE):
        loc = _clean_candidate(m.group(1))
        if loc:
            candidates.append(loc)

    # Dédupliquer tout en gardant l'ordre
    seen = set()
    result = []
    for c in candidates:
        k = norm(c)
        if k not in seen and not is_too_vague_for_geocoding(c):
            seen.add(k)
            result.append(c)
    return result

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

    # Trop à l'ouest pour ce jeu de données (Amériques ; Cape Verde = lon ~-25)
    if lon < -25.5:
        return True, "TOO_FAR_WEST"

    # Boîte géographique spécifique à ce jeu de données :
    # Espagne / Maroc / Algérie / Sahara occidental / Mauritanie / Sénégal / Cap-Vert
    # lat 10-44, lon -25.5 à 15
    if lat > 44:
        return True, "TOO_FAR_NORTH"
    if lat < 10:
        return True, "TOO_FAR_SOUTH"
    if lon > 15:
        return True, "TOO_FAR_EAST"

    return False, "OK"

def parse_int_value(value):
    """Parse an integer from CSV values like '11', '11.0', or '11 people'."""
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


def _ascii_norm_text(value):
    if value is None:
        return ""
    txt = unicodedata.normalize("NFKD", str(value))
    txt = "".join(ch for ch in txt if not unicodedata.combining(ch))
    txt = re.sub(r"\s+", " ", txt).strip().lower()
    return txt


def _is_plural_gender_context(text_ascii):
    return any(
        token in text_ascii
        for token in (
            " hombres ", " mujeres ", " jovenes ", " menores ", " ninos ", " ninas ",
            " personas ", " supervivientes ",
        )
    )


def infer_gender_from_nota(nota_text, default_dead_missing_count):
    """Return 'male'/'female'/None from narrative with ambiguity safeguards."""
    txt = f" {_ascii_norm_text(nota_text)} "
    if not txt.strip():
        return None

    # On évite d'assigner un genre unique sur des récits collectifs ambigus.
    if default_dead_missing_count and default_dead_missing_count > 1 and _is_plural_gender_context(txt):
        return None

    male_patterns = (
        r"\bun hombre\b", r"\bun joven\b", r"\bun chico\b", r"\bvaron\b", r"\bmasculin",
        r"\bde origen magrebi\b", r"\bde origen sirio\b",
    )
    female_patterns = (
        r"\buna mujer\b", r"\buna chica\b", r"\buna nina\b", r"\bfemenin",
    )
    male_hit = any(re.search(p, txt) for p in male_patterns)
    female_hit = any(re.search(p, txt) for p in female_patterns)
    if male_hit and not female_hit:
        return "male"
    if female_hit and not male_hit:
        return "female"
    return None


def infer_age_from_nota(nota_text, default_dead_missing_count):
    """Infer a single numeric age in years when confidence is high."""
    txt = _ascii_norm_text(nota_text)
    if not txt:
        return None

    # Sur les événements collectifs, n'inférer que si un âge explicite unique est trouvé.
    if default_dead_missing_count and default_dead_missing_count > 1:
        pass

    # Exclure les âges ambigus type "20 o 25 anos".
    if re.search(r"\b\d{1,2}\s*(?:o|/|-)\s*\d{1,2}\s*anos\b", txt):
        return None

    # "de 17 anos", "17 anos", "con 23 anos"
    for pat in (
        r"\bde\s+(\d{1,2})\s+anos\b",
        r"\bcon\s+(\d{1,2})\s+anos\b",
        r"\bunos?\s+(\d{1,2})\s+anos\b",
        r"\b(\d{1,2})\s+anos\b",
    ):
        m = re.search(pat, txt)
        if m:
            age = int(m.group(1))
            if 0 <= age <= 100:
                return age

    # "nina de 8 meses" -> 0 an
    m_month = re.search(r"\b(\d{1,2})\s+mes(?:es)?\b", txt)
    if m_month:
        months = int(m_month.group(1))
        if 0 <= months < 24:
            return 0

    return None


def infer_missing_count_from_nota(nota_text):
    txt = _ascii_norm_text(nota_text)
    if not txt:
        return 0
    if not re.search(r"desaparec|sin noticias|no se sabe nada|buscan a|busqueda", txt):
        return 0

    m = re.search(r"(?:desaparec(?:en|ieron|ido|ida|idos|idas)?|desaparicion de)\s+(\d{1,3})\b", txt)
    if m:
        try:
            return max(1, int(m.group(1)))
        except Exception:
            return 1
    return 1


def infer_transport_label_from_text(nota_text):
    """
    Détecte le type de transport dans le texte NOTA (espagnol) 
    et retourne un label qui existe dans le thésaurus (smallBoat, car, truck, bus, train).
    Retourne "human" pour les transports humains (à exclure).
    Retourne None si pas de transport détecté.
    """
    txt = f" {_ascii_norm_text(nota_text)} "
    if not txt.strip():
        return None

    # Bateaux/ferries en espagnol
    if any(k in txt for k in (" patera ", " cayuco ", " embarcacion ", " barca ", " pesquero ", " barco ", " ferry ")):
           return "small boat"
    
    # Camions en espagnol
    if any(k in txt for k in (" camion ", " camioneta ")):
        return "truck"
    
    # Trains en espagnol
    if any(k in txt for k in (" tren ", " ferrovi", " ferrocarril ")):
        return "train"
    
    # Bus en espagnol
    if any(k in txt for k in (" autobus ", " bus ", " autocar ")):
        return "bus"
    
    # Voitures en espagnol (coche, auto, vehículo, carro)
    if any(k in txt for k in (" coche ", " auto ", " vehiculo ", " carro ")):
        return "car"
    
    # Transports humains en espagnol - à ignorer (ne pas créer de Transport)
    if any(k in txt for k in (" a nado ", " nadando ", " nado ", " nadar ", " a pie ", " caminando ")):
        return "human"
    
    return None

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
    sval = re.sub(r'[^A-Za-z0-9]', '', val).upper()
    try:
        if re.fullmatch(r'[A-Z]{2}', sval):
            c = pycountry.countries.get(alpha_2=sval)
            if c:
                cc = c
        elif re.fullmatch(r'[A-Z]{3}', sval):
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
        uri = DATA["espagne_frontera_sur_Country_" + iso3.upper()]
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
    uri = DATA["espagne_frontera_sur_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(country_code_or_name)))
    return uri

def create_age_node(g, age_value, age_uri=None):
    """Create an Age node (URI preferred for graph browsing) and return it."""
    if age_value is None or is_missing(age_value):
        return None
    try:
        age_num = int(float(str(age_value).strip()))
    except Exception:
        return None
    node = age_uri if age_uri is not None else BNode()
    g.add((node, RDF.type, F.Age))
    g.add((node, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    return node

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
    Load optional CSV mapping: col1=espagne_frontera_sur_value, col2=Thesaurus_prefLabel
    Returns dict: normalized_espagne_frontera_sur_value -> normalized_thesaurus_label
    """
    mapping = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping
    try:
        mdf = pd.read_csv(mapping_path, sep=";", dtype=str)
        cols = list(mdf.columns)
        if len(cols) >= 2:
            espagne_frontera_sur_col = cols[0]
            thes_col = cols[1]
            for _, r in mdf.iterrows():
                a = norm(r.get(espagne_frontera_sur_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
            print(f"Loaded {len(mapping)} espagne_frontera_sur->Thesaurus mappings from CSV")
            print(f"Columns used: '{espagne_frontera_sur_col}' -> '{thes_col}'")
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

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
DEATH_INJURY_CLASS = find_by_label(g_ref, "Death injury") or find_by_label(g_ref, "Mort blessure") or F.DeathInjury
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or find_by_label(g_ref, "Blessure") or F.Injury
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
PROP_numberDead = find_by_label(g_ref, "number dead") or F.numberDead
PROP_numberMissing = find_by_label(g_ref, "number of missing") or F.numberMissing
PROP_totalDeadAndMissing = find_by_label(g_ref, "total dead and missing") or F.totalDeadAndMissing
PROP_hasDeathCountry = find_by_label(g_ref, "hasDeathCountry") or F.hasDeathCountry
PROP_hasInhumationCountry = find_by_label(g_ref, "hasInhumationCountry") or F.hasInhumationCountry

SOURCE_TYPE_FAMILY = find_by_label(g_ref, "Family") or F.Family
SOURCE_TYPE_MEDIA = find_by_label(g_ref, "Media") or F.Media
SOURCE_TYPE_CIVIL_SOCIETY = find_by_label(g_ref, "Civil society") or F.CivilSociety
SOURCE_TYPE_OFFICIAL_DOCUMENT = find_by_label(g_ref, "Official document") or F.OfficialDocument
SOURCE_TYPE_OTHER_OFFICIAL_DOCUMENT = find_by_label(g_ref, "Other official document") or F.OtherOfficialDocument
SOURCE_TYPE_DEATH_CERTIFICATE = find_by_label(g_ref, "Death certificate") or F.DeathCertificate

THES_male = find_thesaurus_term_by_prefLabel_fr(g_ref, "male") or find_thesaurus_term_by_prefLabel_fr(g_ref, "homme") or T.male
THES_female = find_thesaurus_term_by_prefLabel_fr(g_ref, "female") or find_thesaurus_term_by_prefLabel_fr(g_ref, "femme") or T.female
MISSING_EVENT_CLASS = F.Missing
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation", "CorpseRepatriation"])

# Renforce les patrons pour le corpus espagnol.
for _spec in ADDITIONAL_EVENT_SPECS:
    _name = _spec.get("name")
    if _name == "CorpseAnalysis":
        _spec["patterns"].extend([r"\bautopsia\b", r"\bnecropsia\b", r"\banalisis del cuerpo\b", r"\bidentificacion del cadaver\b"])
    elif _name == "Call":
        _spec["patterns"].extend([r"\bllamad(?:a|o|as|os)?\b", r"\btelefono\b", r"\bllamo\b"])
    elif _name == "Control":
        _spec["patterns"].extend([r"\bcontrol policial\b", r"\bguardia civil\b", r"\bdetenid[oa]s?\b", r"\binterceptad[oa]s?\b"])
    elif _name == "Conversation":
        _spec["patterns"].extend([r"\bconversacion\b", r"\bhabl(?:a|aron|o)\b", r"\brelat(?:a|an|aron)\b"])
    elif _name == "Trace":
        _spec["patterns"].extend([r"\brastro\b", r"\bsin rastro\b", r"\bsin noticias\b"])
    elif _name == "Testimony":
        _spec["patterns"].extend([r"\btestimonio\b", r"\bsegun\b", r"\bsegun los supervivientes\b"])

if (MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_EVENT_CLASS, RDFS.subClassOf, F.IndividualEvent))
    g.add((MISSING_EVENT_CLASS, RDFS.label, Literal("Missing", lang="en")))

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
    # Calculer le nombre de personnes à créer (morts + disparus)
    muerto_count_preview = parse_int_value(row.get("MUERTO", ""))
    desaparecido_count_preview = parse_int_value(row.get("DESAPARECIDO", ""))
    muerto_count_preview = max(0, muerto_count_preview or 0)
    desaparecido_count_preview = max(0, desaparecido_count_preview or 0)
    
    # Fallback Missing par analyse textuelle si la colonne est vide.
    if desaparecido_count_preview == 0:
        desaparecido_count_preview = infer_missing_count_from_nota(row.get("NOTA", "") or row.get("nota", ""))
    
    total_persons_count = muerto_count_preview + desaparecido_count_preview
    
    # Créer une liste de tuples (person_uri, event_uri) pour chaque personne de cette ligne
    # Les tuples seront réutilisés pour appliquer les propriétés communes
    persons_events = []
    
    # Créer les Persons et leurs Death events
    for person_idx in range(muerto_count_preview):
        person_uri = DATA["espagne_frontera_sur_Person_%d_%d" % (idx+1, person_idx+1)]
        g.add((person_uri, RDF.type, PERSON_CLASS))
        count_person += 1
        
        event_uri = DATA[f"espagne_Death_{idx+1}_{person_idx+1}"]
        if str(event_uri) not in created_death_events:
            g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
            g.add((event_uri, RDF.type, DEATH_INJURY_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_death_events[str(event_uri)] = event_uri
            count_death_events += 1
        
        # Lier cette personne à son event
        g.add((person_uri, PROP_composedOf, event_uri))
        persons_events.append((person_uri, event_uri))
    
    # Créer les Persons et leurs Missing events
    for person_idx in range(desaparecido_count_preview):
        person_uri = DATA["espagne_frontera_sur_Person_%d_%d" % (idx+1, muerto_count_preview + person_idx + 1)]
        g.add((person_uri, RDF.type, PERSON_CLASS))
        count_person += 1
        
        event_uri = DATA[f"espagne_Missing_{idx+1}_{person_idx+1}"]
        if str(event_uri) not in created_death_events:
            g.add((event_uri, RDF.type, MISSING_EVENT_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_death_events[str(event_uri)] = event_uri
            count_death_events += 1
        
        # Lier cette personne à son event
        g.add((person_uri, PROP_composedOf, event_uri))
        persons_events.append((person_uri, event_uri))
    
    # Si pas de persons créées, skip le reste (aucun mort ni disparu)
    if not persons_events:
        continue

    embark_uri = None
    repatriation_event_uri = None
    inhumation_event_uri = None

    # Appliquer les propriétés communes à TOUTES les Persons créées depuis cette ligne
    for person_uri, _ in persons_events:
        # NOMS
        val = row.get("Nom_connu", "")
        if val and not is_missing(val):
            g.add((person_uri, PROP_hasName, Literal(str(val).strip())))

        val = row.get("Nom_non_public", "")
        if val and not is_missing(val):
            g.add((person_uri, PROP_hasOfficialName, Literal(str(val).strip())))

        val = row.get("Autre_nom", "")
        if val and not is_missing(val):
            g.add((person_uri, PROP_otherName, Literal(str(val).strip())))

    # AGE - créer et appliquer le nœud d'âge à TOUTES les Persons
    age_node = None
    age_val = row.get("Age", "")
    try:
        age_uri = DATA[f"espagne_frontera_sur_Age_{idx+1}"]
        if age_val is not None and age_val != "" and not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
            age_node = create_age_node(g, age_val, age_uri=age_uri)
        else:
            age_from_nota = infer_age_from_nota(row.get("NOTA", "") or row.get("nota", ""), total_persons_count)
            if age_from_nota is not None:
                age_node = create_age_node(g, age_from_nota, age_uri=age_uri)
        if age_node:
            for person_uri, _ in persons_events:
                g.add((person_uri, PROP_hasAgeLink, age_node))
                # Lien direct pour améliorer la visibilité dans GraphDB.
                for age_v in g.objects(age_node, F.hasAge):
                    g.add((person_uri, F.hasAge, age_v))
    except Exception:
        pass

    # SEXE (inference textuelle depuis NOTA) - appliquer à TOUTES les Persons
    gender_text = row.get("NOTA", "") or row.get("Nota", "") or row.get("Description", "")
    inferred_gender = infer_gender_from_nota(gender_text, total_persons_count)
    if inferred_gender == "male":
        if THES_male is not None:
            for person_uri, _ in persons_events:
                g.add((person_uri, F.gender, THES_male))
        else:
            for person_uri, _ in persons_events:
                g.add((person_uri, F.gender, Literal("male")))
    elif inferred_gender == "female":
        if THES_female is not None:
            for person_uri, _ in persons_events:
                g.add((person_uri, F.gender, THES_female))
        else:
            for person_uri, _ in persons_events:
                g.add((person_uri, F.gender, Literal("female")))

    # LIEU DE NAISSANCE
    birth_country = None
    if not is_missing(row.get("Pays_naissance", "")):
        birth_country = ensure_country_node(g, row.get("Pays_naissance"))
    elif not is_missing(row.get("Nati", "")):
        birth_country = ensure_country_node(g, row.get("Nati"))
    if birth_country:
        for person_uri, _ in persons_events:
            g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES
    comment_cdb = row.get("Commentaire CDB", "") or row.get("Commentaire_CDB", "")
    if comment_cdb and not is_missing(comment_cdb):
        for person_uri, _ in persons_events:
            g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))
    
    comment_sb = row.get("Commentaire SB", "") or row.get("Commentaire_SB", "")
    if comment_sb and not is_missing(comment_sb):
        for person_uri, _ in persons_events:
            g.add((person_uri, PROP_hasComment, Literal(str(comment_sb).strip())))

    # LIEU DE NAISSANCE
    birth_country = None
    if not is_missing(row.get("Pays_naissance", "")):
        birth_country = ensure_country_node(g, row.get("Pays_naissance"))
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

    # Collecter les URIs des events (Death et Missing) pour les propriétés communes
    event_uris = [event_uri for _, event_uri in persons_events]
    
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Cause_deces", "LUGAR", "ZONA", "Pays_mort"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Commentaire CDB", "Commentaire SB"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["NOTA", "nota", "FUENTE", "FUENTE2", "FUENTE3"], is_missing))

    # Réutiliser les mêmes compteurs que pour la création des persons/events,
    # afin de garder CollectiveEvent cohérent avec les événements réellement générés.
    muerto_count = max(0, int(muerto_count_preview or 0))
    desaparecido_count = max(0, int(desaparecido_count_preview or 0))

    additional_counts = add_additional_typed_events(
        g,
        persons_events,
        None,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "espagne",
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

    # Evenement d'ancrage pour les liens optionnels de ligne qui attendent une URI d'evenement unique
    event_uri = event_uris[0] if event_uris else None

    # DATE DE DÉCÈS (FECHA)
    fecha_val = row.get("FECHA", "") or row.get("fecha", "")
    if fecha_val and not is_missing(fecha_val):
        try:
            date_str = str(fecha_val).strip()
            parsed_date = None

            # Try common formats in this dataset first
            for fmt in ("%d/%m/%Y", "%d-%m-%Y", "%Y-%m-%d"):
                try:
                    parsed_date = datetime.strptime(date_str, fmt)
                    break
                except ValueError:
                    continue

            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str.split()[0], "%Y-%m-%d")
                except (ValueError, IndexError):
                    pass

            if parsed_date:
                date_iso = parsed_date.strftime("%Y-%m-%d")
                weekday_name = infer_day_of_week_name(date_iso)
                for ev_uri in event_uris:
                    g.add((ev_uri, TIME.inXSDDate, Literal(date_iso, datatype=XSD.date)))
                    if weekday_name:
                        g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name]))
                        g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                        g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
        except Exception as e:
            print(f"Erreur parsing date pour ligne {idx+1}: {fecha_val} - {e}")

    # CAUSE DE DÉCÈS (nouveau mapping avec thésaurus)
    cause_deces_val = row.get("Cause_deces", "") or row.get("cause_deces", "")
    if cause_deces_val and not is_missing(cause_deces_val):
        uri, lbl, is_literal = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        if uri:
            # Triple: Death hasDeathCause avec URI du thesaurus
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, uri))
            count_cause_matched += 1
        elif lbl:
            # Repli: valeur litterale
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, Literal(lbl)))
            count_cause_literal += 1
        
        # Détection d'accidents de circulation
        is_accident, transport_type = detect_traffic_accident_and_transport(cause_deces_val)
        if is_accident:
            count_traffic_accidents += 1
            if transport_type:
                count_transport_identified += 1
    
    # CERTIFICAT DE DÉCÈS
    acte_deces_val = row.get("Acte_deces", "") or row.get("acte_deces", "")
    if acte_deces_val and not is_missing(acte_deces_val) and event_uris:
        certificate_uri = DATA["DeathCertificate_%d" % (idx+1)]
        g.add((certificate_uri, RDF.type, DEATH_CERTIFICATE_CLASS))
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_certificate, certificate_uri))
        g.add((certificate_uri, PROP_hasIdCertificate, Literal(str(acte_deces_val).strip())))
        count_death_certificates += 1

    # frontiere_EX -> borderOUT
    front_ex = row.get("Frontiere_EX", "") or row.get("frontiere_EX", "") or row.get("frontiere_EX".lower(), "")
    if not is_missing(front_ex) and event_uri is not None:
        cnode = ensure_country_node(g, str(front_ex).strip())
        if cnode:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_borderOUT, cnode))

    # frontiere_IN -> borderIN
    front_in = row.get("Frontiere_IN", "") or row.get("frontiere_IN", "") or row.get("frontiere_IN".lower(), "")
    if not is_missing(front_in) and event_uri is not None:
        cnode = ensure_country_node(g, str(front_in).strip())
        if cnode:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_borderIN, cnode))

    # GEO depuis LUGAR, repli sur ZONA puis NOTA
    lugar_val = row.get("LUGAR", "") or row.get("lugar", "")
    zona_val = row.get("ZONA", "") or row.get("zona", "")
    nota_val = row.get("NOTA", "") or row.get("nota", "")

    # Construire la liste de candidats géocodage par ordre de priorité:
    # 1) LUGAR en priorité
    # 2) Si NOTA contient un lieu plus précis que LUGAR, le tester avant LUGAR
    # 3) Si pas de LUGAR, fallback sur ZONA
    geocode_candidates = []
    zona_text = str(zona_val).strip() if not is_missing(zona_val) else ""

    # Mapping ZONA → hint pays pour le géocodage (forcer le bon contexte géographique)
    _ZONA_GEOCODE_COUNTRY_HINTS = {
        "marruecos": "Morocco",
        "maroc": "Morocco",
        "argelia": "Algeria",
        "senegal": "Senegal",
        "mauritania": "Mauritania",
        "cabo verde": "Cape Verde",
        "sahara": "Western Sahara",
        "nador": "Morocco",
        "canarias": "Spain",
        "ceuta": "Spain",
        "melilla": "Spain",
        "almeria": "Spain",
        "almería": "Spain",
        "cadiz": "Spain",
        "cádiz": "Spain",
        "malaga": "Spain",
        "málaga": "Spain",
        "granada": "Spain",
        "levante": "Spain",
        "baleares": "Spain",
    }
    country_hint_for_zona = _ZONA_GEOCODE_COUNTRY_HINTS.get(norm(zona_text)) if zona_text else None

    # Le hint de géocodage est le nom du pays correspondant à ZONA si disponible,
    # sinon le nom brut de ZONA (pour disambiguer ex: "Cartagena, Spain" vs Colombie)
    zona_hint = country_hint_for_zona or (str(zona_val).strip() if not is_missing(zona_val) else None)
    lugar_text = str(lugar_val).strip() if not is_missing(lugar_val) else ""

    def _add_candidate(txt, hint):
        if is_missing(txt):
            return
        cand = str(txt).strip()
        if not cand or is_too_vague_for_geocoding(cand):
            return
        if any(norm(cand) == norm(existing) for existing, _ in geocode_candidates):
            return
        geocode_candidates.append((cand, hint))

    def _specificity_score(txt):
        if is_missing(txt):
            return 0
        s = str(txt).strip()
        s_norm = norm(s)
        if not s_norm:
            return 0
        score = 1
        if not is_macro_location_label(s):
            score += 3
        # Plus il y a de tokens (raisonnables), plus on suppose un lieu précis.
        tokens = [t for t in re.split(r"[\s,\-/]+", s_norm) if t]
        score += min(3, len(tokens))
        # Ex: "Mauritania-Nouadhibou" ou "Chiclana, Cádiz".
        if "-" in s or "," in s:
            score += 1
        return score

    nota_locs = extract_location_from_nota(nota_val)
    if lugar_text:
        lugar_score = _specificity_score(lugar_text)
        # Si NOTA est plus précis que LUGAR, on le tente d'abord.
        better_nota = None
        better_score = lugar_score
        for nota_loc in nota_locs:
            n_score = _specificity_score(nota_loc)
            if n_score > better_score:
                better_nota = nota_loc
                better_score = n_score
        if better_nota:
            _add_candidate(better_nota, zona_hint if zona_hint and norm(zona_hint) != norm(better_nota) else None)

        # Utiliser ZONA comme hint pour disambiguer (ex: "Chiclana, Cádiz").
        # Prétraiter le LUGAR (traduction pays espagnol, décomposition "Pays-Ville")
        for _lt, _lh in _preprocess_lugar_for_geocoding(lugar_text, country_hint=zona_hint):
            _add_candidate(_lt, _lh if _lh and norm(_lh) != norm(_lt) else zona_hint)

        # Fallback secondaire sur ZONA puis autres lieux extraits de NOTA.
        if zona_text and norm(zona_text) != norm(lugar_text):
            _add_candidate(zona_text, None)
        for nota_loc in nota_locs:
            _add_candidate(nota_loc, zona_hint if zona_hint and norm(zona_hint) != norm(nota_loc) else None)
    else:
        # Pas de LUGAR -> fallback sur ZONA.
        if zona_text:
            _add_candidate(zona_text, None)
        for nota_loc in nota_locs:
            _add_candidate(nota_loc, zona_hint if zona_hint and norm(zona_hint) != norm(nota_loc) else None)

    geometry_added = False
    # Bounding box ZONA pour valider la cohérence spatiale de LUGAR
    _zona_bbox = None
    if zona_text:
        _zona_bbox = _ZONA_BOUNDING_BOXES.get(norm(zona_text))

    def _in_zona_bbox(lat_v, lon_v):
        """Retourne True si les coordonnées sont dans la bounding box ZONA (avec marge)."""
        if _zona_bbox is None:
            return True  # Pas de contrainte si ZONA inconnue
        lat_min, lat_max, lon_min, lon_max = _zona_bbox
        m = ZONA_BBOX_MARGIN
        return (lat_min - m <= lat_v <= lat_max + m) and (lon_min - m <= lon_v <= lon_max + m)

    for geocode_text, hint in geocode_candidates:
        if _is_macro_fallback_label(geocode_text):
            continue
        try:
            lat_f, lon_f = geocode_location(geocode_text, region_hint=hint, zona_bbox=_zona_bbox)
            if lat_f is not None and lon_f is not None and math.isfinite(lat_f) and math.isfinite(lon_f):
                # Validation ZONA : si les coordonnées ne sont pas dans la zone attendue, on ignore ce résultat.
                if not _in_zona_bbox(lat_f, lon_f):
                    print(f"  ⚠️  LUGAR '{geocode_text}' géocodé hors ZONA '{zona_text}' ({lat_f:.2f},{lon_f:.2f}) → ignoré")
                    continue
                wkt = build_wkt_for_location_precision(
                    geocode_text,
                    lat_f,
                    lon_f,
                    USE_BOUNDARY_WKT_FOR_GEOCODED,
                )
                wkt = _coerce_event_wkt(geocode_text, wkt, lat_f, lon_f)
                for ev_pos, ev_uri in enumerate(event_uris, start=1):
                    geometry_uri = DATA[f"espagne_geometry_{idx+1}_{ev_pos}"]
                    g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                    g.add((geometry_uri, RDF.type, GEO.Geometry))
                    g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
                    # Localisation géocodée (coordonnées approchées) → précision faible
                    g.add((geometry_uri, F.hasPrecision, Literal(False, datatype=XSD.boolean)))
                    g.add((ev_uri, F.lieu, Literal(str(geocode_text).strip())))
                geometry_added = bool(event_uris)
                break  # Stop dès qu'on a des coordonnées valides
        except Exception:
            continue

    # Fallback géométrique: garantir une géométrie pour chaque événement
    # même si aucun candidat LUGAR n'a pu être retenu.
    if (not geometry_added) and event_uris:
        fallback_wkt = None
        fallback_label = None

        # Priorité 1: retenter les candidats LUGAR avec un filtre moins strict
        # (sans bbox dans le cache/lookup), puis vérifier nous-mêmes la cohérence ZONA.
        for fb_text, fb_hint in geocode_candidates:
            if _is_macro_fallback_label(fb_text):
                continue
            try:
                lat_fb, lon_fb = geocode_location(fb_text, region_hint=fb_hint, zona_bbox=None)
                if lat_fb is None or lon_fb is None:
                    continue
                if not (math.isfinite(lat_fb) and math.isfinite(lon_fb)):
                    continue
                is_susp_fb, _ = is_suspicious_coordinate(lat_fb, lon_fb)
                if is_susp_fb:
                    continue
                if not _in_zona_bbox(lat_fb, lon_fb):
                    continue
                fallback_wkt = build_wkt_for_location_precision(
                    fb_text,
                    lat_fb,
                    lon_fb,
                    USE_BOUNDARY_WKT_FOR_GEOCODED,
                )
                fallback_wkt = _coerce_event_wkt(fb_text, fallback_wkt, lat_fb, lon_fb)
                fallback_label = fb_text
                break
            except Exception:
                continue

        # Priorité 2: ZONA -> toujours un POINT (jamais de polygone bbox/carré).
        if fallback_wkt is None and _zona_bbox is not None:
            lat_min, lat_max, lon_min, lon_max = _zona_bbox
            lat_c = (lat_min + lat_max) / 2.0
            lon_c = (lon_min + lon_max) / 2.0
            fallback_wkt = f"POINT({lon_c} {lat_c})"
            fallback_label = zona_text or "ZONA"

        if fallback_wkt is None:
            # Priorité 3: point sur ZONA puis pays de mort.
            fallback_queries = []
            if zona_text and not _is_macro_fallback_label(zona_text):
                fallback_queries.append((zona_text, zona_hint))
            pays_mort_val = row.get("Pays_mort", "") or row.get("pays_mort", "") or row.get("Pays_mort".lower(), "")
            if not is_missing(pays_mort_val) and not _is_macro_fallback_label(pays_mort_val):
                fallback_queries.append((str(pays_mort_val).strip(), None))

            for fb_text, fb_hint in fallback_queries:
                try:
                    lat_fb, lon_fb = geocode_location(fb_text, region_hint=fb_hint)
                    if lat_fb is None or lon_fb is None:
                        continue
                    if not (math.isfinite(lat_fb) and math.isfinite(lon_fb)):
                        continue
                    is_susp_fb, _ = is_suspicious_coordinate(lat_fb, lon_fb)
                    if is_susp_fb:
                        continue
                    fallback_wkt = f"POINT({lon_fb} {lat_fb})"
                    fallback_label = fb_text
                    break
                except Exception:
                    continue

        if fallback_wkt and _is_macro_fallback_label(fallback_label):
            # Macro-pays/zone labels are too coarse: keep event unlocalized on map.
            fallback_wkt = None
            fallback_label = None

        if fallback_wkt:
            for ev_pos, ev_uri in enumerate(event_uris, start=1):
                geometry_uri = DATA[f"espagne_geometry_{idx+1}_{ev_pos}"]
                g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                g.add((geometry_uri, RDF.type, GEO.Geometry))
                g.add((geometry_uri, GEO.asWKT, Literal(fallback_wkt, datatype=GEO.wktLiteral)))
                g.add((geometry_uri, F.hasPrecision, Literal(False, datatype=XSD.boolean)))
                if fallback_label:
                    g.add((ev_uri, F.lieu, Literal(str(fallback_label).strip())))
            geometry_added = True
        else:
            # No geometry fallback for macro/unknown locations: event stays unlocalized.
            geometry_added = False

    pays_mort = row.get("Pays_mort", "") or row.get("pays_mort", "") or row.get("Pays_mort".lower(), "")
    if (not geometry_added) and not is_missing(pays_mort) and event_uri is not None:
        country_node = ensure_country_node(g, str(pays_mort).strip())
        if country_node:
            for ev_uri in event_uris:
                g.add((ev_uri, F.paysMort, country_node))

    # Garantir hasDeathCountry pour toutes les occurrences de Death.
    death_country_node = None
    if not is_missing(pays_mort):
        death_country_node = ensure_country_node(g, str(pays_mort).strip())
    if death_country_node is None and not is_missing(zona_val):
        death_country_node = ensure_country_node(g, str(zona_val).strip())
    if death_country_node:
        for ev_uri in event_uris:
            if (ev_uri, RDF.type, DEATH_EVENT_CLASS) in g:
                g.add((ev_uri, PROP_hasDeathCountry, death_country_node))

    # TRANSPORT - créer seulement pour les vrais moyens de transport (bateau, voiture, etc.)
    # Ignorer les "transports humains" (marche, nage, pied) et ne rien créer si pas spécifié
    transport_val = row.get("transport", "") or row.get("Transport", "") or row.get("transport".lower(), "")
    if is_missing(transport_val):
        transport_val = infer_transport_label_from_text(nota_val)
    
    if not is_missing(transport_val):
        t_norm = norm(transport_val)
        # Ignorer les transports humains (marche, nage, pied) - ne rien créer
        is_human_transport = any(keyword in t_norm for keyword in ["marche", "nage", "pied", "humain", "à pied"])
        
        if not is_human_transport:
            # Chercher le transport dans le thesaurus
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
            
            # Créer un Transport node seulement si trouvé dans le thesaurus et c'est un vrai transport
            if th_term is not None:
                th_term_label = str(th_term).lower()
                # Exclure les faux transports: human, humain, personne
                if not any(keyword in th_term_label for keyword in ["human", "humain", "personne"]):
                    slug = re.sub(r'[^a-z0-9_]', '_', norm(transport_val))
                    if slug and slug not in ("nan", "none", ""):
                        transport_uri = DATA["espagne_frontera_sur_Transport_" + slug + "_" + str(idx+1)]
                        if str(transport_uri) not in created_transports:
                            g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
                            g.add((transport_uri, RDF.type, th_term))
                            created_transports[str(transport_uri)] = transport_uri
                            count_transports += 1
                        
                        # Lier chaque événement au transport
                        for ev_uri in event_uris:
                            g.add((ev_uri, PROP_transportType, transport_uri))
                            # Lien direct Transport -> Event (Death/Missing), conforme à l'ontologie UsedIn.
                            g.add((transport_uri, PROP_usedIn, ev_uri))

                        # Créer un événement d'embarquement pour chaque personne
                        for person_idx, (person_uri, death_event_uri) in enumerate(persons_events):
                            embark_uri = DATA["EmbarkEvent_%d_%d_%s" % (idx+1, person_idx+1, slug)]
                            if (embark_uri, None, None) not in g:
                                g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                            g.add((embark_uri, PROP_usedIn, transport_uri))
                            # Ajouter aussi le sens ontologique attendu.
                            g.add((transport_uri, PROP_usedIn, embark_uri))
                            if death_event_uri is not None:
                                g.add((embark_uri, PROP_temporal_before, death_event_uri))
                                g.add((death_event_uri, PROP_temporal_after, embark_uri))
                            g.add((person_uri, PROP_composedOf, embark_uri))
                            count_embark += 1

    # COLLECTIVE EVENT when MUERTO + DESAPARECIDO >= 2
    total_dead_missing = muerto_count + desaparecido_count
    if total_dead_missing >= 2 and event_uris:
        collective_event_uri = DATA[f"espagne_CollectiveEvent_{idx+1}"]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            g.add((collective_event_uri, PROP_numberDead, Literal(muerto_count, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_numberMissing, Literal(desaparecido_count, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_totalDeadAndMissing, Literal(total_dead_missing, datatype=XSD.integer)))
            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1

            recit_val = row.get("NOTA", "") or row.get("nota", "") or row.get("Recit_passage_deces", "") or row.get("recit_passage_deces", "")
            if recit_val and not is_missing(recit_val):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(recit_val).strip())))

        # Lier les events au CollectiveEvent
        for ev_uri in event_uris:
            g.add((ev_uri, F.group, collective_event_uri))
        
        # Lier les Persons au CollectiveEvent
        for person_uri, _ in persons_events:
            g.add((collective_event_uri, F.involves, person_uri))
        
        if embark_uri is not None:
            g.add((embark_uri, F.group, collective_event_uri))

    # RAPATRIEMENT — depuis colonne Enterrement (rarement présente) OU depuis NOTA
    enterrement_text = str(row.get("Enterrement", "")).strip()
    nota_norm = norm(nota_val)
    has_repatriation = (
        ("rapatrié" in norm(enterrement_text) or "rapatriement" in norm(enterrement_text))
        and "?" not in enterrement_text
    ) or any(k in nota_norm for k in ("repatriado", "repatriación", "repatriacion", "devuelto al pais"))
    if has_repatriation and event_uris:
        for person_idx, (person_uri, _) in enumerate(persons_events):
            repatriation_event_uri = DATA["espagne_frontera_sur_Repatriation_%d_%d" % (idx+1, person_idx+1)]
            g.add((repatriation_event_uri, RDF.type, F.Repatriation))
            g.add((repatriation_event_uri, RDF.type, F.IndividualEvent))
            g.add((person_uri, PROP_composedOf, repatriation_event_uri))
            if event_uri is not None:
                g.add((event_uri, TEMP.before, repatriation_event_uri))
                g.add((repatriation_event_uri, PROP_temporal_after, event_uri))
            if birth_country:
                g.add((repatriation_event_uri, PROP_targetCountry, birth_country))
            count_repatriation += 1

    # INHUMATION — depuis colonne Comm_enterrement OU depuis mots-clés NOTA (entierro/entierran/enterraron)
    comm_enterrement = row.get("Comm_enterrement", "")
    has_inhumation_nota = any(k in nota_norm for k in (
        "entierran", "entierro", "enterraron", "enterrado", "enterrada",
        "enterr", "sepultado", "sepultada", "inhumado", "inhumada",
    ))
    if (comm_enterrement and not is_missing(comm_enterrement)) or (has_inhumation_nota and event_uris):
        # Récupérer les coordonnées existantes
        lat_ent = row.get("Coord_Lat_enterrement", "") or row.get("Coord_lat_enterrement", "")
        lon_ent = row.get("Coord_Long_enterrement", "") or row.get("Coord_long_enterrement", "")
        
        lat_e = None
        lon_e = None
        inhumation_geocoded_fallback = False
        geocode_src = None
        
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
        
        # Si pas de coordonnées, tenter d'abord un cimetière (Comm_enterrement),
        # puis fallback sur géocodage normal.
        if lat_e is None or lon_e is None:
            geocode_src = str(comm_enterrement).strip() if comm_enterrement and not is_missing(comm_enterrement) else (str(lugar_val).strip() if not is_missing(lugar_val) else None)
            if geocode_src:
                zona_hint_inh = str(zona_val).strip() if not is_missing(zona_val) and norm(zona_val) != norm(geocode_src) else None
                lat_e, lon_e = geocode_cemetery_location(geocode_src, region_hint=zona_hint_inh)
                if lat_e is not None and lon_e is not None:
                    inhumation_geocoded_fallback = True
                    print(f"Géocodé inhumation '{geocode_src}' -> ({lat_e}, {lon_e})")
        
        # Préparer la géométrie (commune à toutes les inhumations de la ligne)
        wkt_ent = None
        inhumation_label = None
        
        # Ajouter la géométrie si coordonnées disponibles
        if lat_e is not None and lon_e is not None and math.isfinite(lat_e) and math.isfinite(lon_e):
            is_susp, reason = is_suspicious_coordinate(lat_e, lon_e)
            if not is_susp:
                inhumation_label = comm_enterrement if (comm_enterrement and not is_missing(comm_enterrement)) else geocode_src
                # Toujours un POINT pour les inhumations (jamais de polygone)
                wkt_ent = f"POINT({lon_e} {lat_e})"
        else:
            # Fallback inhumation: bbox ZONA, sinon bbox globale dataset.
            if _zona_bbox is not None:
                lat_min, lat_max, lon_min, lon_max = _zona_bbox
                # Toujours un POINT sur le centroïde de la bbox ZONA
                lat_c = (lat_min + lat_max) / 2.0
                lon_c = (lon_min + lon_max) / 2.0
                wkt_ent = f"POINT({lon_c} {lat_c})"
                inhumation_label = zona_text or "ZONA"
            else:
                glat_min, glat_max, glon_min, glon_max = GLOBAL_FALLBACK_BBOX
                glat_c = (glat_min + glat_max) / 2.0
                glon_c = (glon_min + glon_max) / 2.0
                wkt_ent = f"POINT({glon_c} {glat_c})"
                inhumation_label = "Dataset fallback"

        if wkt_ent and _is_macro_fallback_label(inhumation_label):
            # Country/large-area labels should not appear as map-localized inhumations.
            wkt_ent = None
            inhumation_label = None
        
        # Créer les inhumation events pour chaque personne
        for person_idx, (person_uri, death_event_uri) in enumerate(persons_events):
            inhumation_event_uri = DATA["InhumationEvent_%d_%d" % (idx+1, person_idx+1)]
            if (inhumation_event_uri, None, None) not in g:
                g.add((inhumation_event_uri, RDF.type, F.Inhumation))
                g.add((inhumation_event_uri, RDF.type, F.IndividualEvent))
            
            g.add((person_uri, PROP_composedOf, inhumation_event_uri))
            
            # Ajouter la géométrie
            if wkt_ent:
                geometry_inhumation_uri = DATA[f"espagne_frontera_sur_geometry_inhumation_{idx+1}_{person_idx+1}"]
                g.add((inhumation_event_uri, GEO.hasGeometry, geometry_inhumation_uri))
                g.add((geometry_inhumation_uri, RDF.type, GEO.Geometry))
                g.add((geometry_inhumation_uri, GEO.asWKT, Literal(wkt_ent, datatype=GEO.wktLiteral)))
                g.add((geometry_inhumation_uri, F.hasPrecision, Literal(not inhumation_geocoded_fallback, datatype=XSD.boolean)))
                if inhumation_label and not is_missing(inhumation_label):
                    g.add((inhumation_event_uri, F.lieu, Literal(str(inhumation_label).strip())))
            
            if event_uri is not None:
                g.add((death_event_uri, TEMP.before, inhumation_event_uri))
                g.add((inhumation_event_uri, PROP_temporal_after, death_event_uri))
            
            count_inhumation += 1

        # Garantir hasInhumationCountry pour tous les inhumation events créés.
        inhum_country_node = None
        if not is_missing(pays_mort):
            inhum_country_node = ensure_country_node(g, str(pays_mort).strip())
        if inhum_country_node is None and not is_missing(zona_val):
            inhum_country_node = ensure_country_node(g, str(zona_val).strip())
        if inhum_country_node:
            for person_idx, _ in enumerate(persons_events):
                inhumation_event_uri = DATA["InhumationEvent_%d_%d" % (idx+1, person_idx+1)]
                g.add((inhumation_event_uri, PROP_hasInhumationCountry, inhum_country_node))

    # SOURCE
    source_candidates = [
        row.get("FUENTE", ""),
        row.get("FUENTE2", ""),
        row.get("FUENTE3", ""),
    ]
    source_urls = []
    for src_val in source_candidates:
        if src_val and not is_missing(src_val):
            source_str = str(src_val).strip().strip('"')
            if source_str.lower().startswith("http"):
                source_urls.append(source_str)

    if source_urls and event_uris:
        source_uri = DATA["espagne_Source_%d" % (idx+1)]
        g.add((source_uri, RDF.type, F.Source))
        source_context = " ".join(
            [
                str(row.get("FUENTE", "") or ""),
                str(row.get("FUENTE2", "") or ""),
                str(row.get("FUENTE3", "") or ""),
                str(row.get("NOTA", "") or row.get("nota", "") or ""),
            ]
        )
        combined_source_text = " ".join(source_urls + [source_context])
        source_category = infer_source_category_key(combined_source_text)
        SOURCE_SUBTYPE_MAP = {
            "family": SOURCE_TYPE_FAMILY,
            "media": SOURCE_TYPE_MEDIA,
            "civil_society": SOURCE_TYPE_CIVIL_SOCIETY,
            "death_certificate": SOURCE_TYPE_DEATH_CERTIFICATE,
            "official_document": SOURCE_TYPE_OFFICIAL_DOCUMENT,
            "other_official_document": SOURCE_TYPE_OTHER_OFFICIAL_DOCUMENT,
        }
        sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
        if sub_type is None:
            # Exigence: chaque source doit appartenir à l'une des 6 catégories.
            sub_type = SOURCE_TYPE_MEDIA
        if sub_type:
            g.add((source_uri, RDF.type, sub_type))
        # Conserver un attribut hasWebLink par colonne source non vide.
        for url in source_urls:
            g.add((source_uri, PROP_hasWebLink, Literal(url)))
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

# --------------------- Resume et sortie ------------------
_save_geocode_cache()
# Sauvegarder le cache boundary WKT sur disque pour accélérer les prochaines exécutions
save_boundary_wkt_cache(BOUNDARY_CACHE_PATH)
count_geom_propagated = propagate_geometry_to_sibling_events(g, F, GEO, RDF, Literal, "espagne_frontera_sur")
count_event_country_from_geometry = add_event_country_from_geometry(g, F, DATA, GEO, RDF, RDFS, Literal, "espagne_frontera_sur")
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "="*60)
print("Import Espagne Frontera Sur complete.")
print("="*60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created: {count_death_events}")
print(f"Transport individuals created: {count_transports}")
print(f"Embark events created: {count_embark}")
print(f"Collective events created: {count_collective_events}")
print(f"Repatriation events created: {count_repatriation}")
print(f"Inhumation events created: {count_inhumation}")
print(f"Sources created: {count_sources}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Death certificates created: {count_death_certificates}")
print(f"\nCause de décès - mapping avec thésaurus:")
print(f"  - Matched to thesaurus URI: {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"\nDétection d'accidents de circulation:")
print(f"  - Accidents détectés (percuté/renversé/accident): {count_traffic_accidents}")
print(f"  - Moyen de transport identifié: {count_transport_identified}")
print(f"Geometry propagated to siblings: {count_geom_propagated}")
print(f"Event countries from geometry: {count_event_country_from_geometry}")
print(f"\nGéocodage (Photon):")
print(f"  - Appels réels : {geocoding_calls_count}")
print(f"  - Depuis cache  : {geocoding_cache_hits}")
print(f"  - Ignorés budget: {geocoding_skipped_budget}")
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

