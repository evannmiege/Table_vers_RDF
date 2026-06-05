#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV Fortress Europe → ontologie RDF selon vos règles.
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
from geopy.geocoders import Photon
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
CSV_PATH = "fortress_europe/fortress_europe.csv"
OUTPUT_TTL = "fortress_europe/frontlet_import_output.ttl"
MAPPING_PATH = "fortress_europe/mappingFeThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)
GEOCODE_CACHE_PATH = "fortress_europe/geocode_cache.json"
GEOCODE_MIN_DELAY_SECONDS = 1.2  # Délai minimal entre 2 requêtes HTTP Photon.
GEOCODE_429_BACKOFF_SECONDS = 8.0  # Pause après un 429 avant un nouvel essai.
GEOCODE_MAX_429_RETRIES = 3  # Nombre d'essais supplémentaires après 429.
GEOCODE_TIME_BUDGET_SEC = 240    # Arrêt du géocodage réseau après N secondes.
GEOCODE_MAX_AFTER_BUDGET = 60    # Appels online supplémentaires après budget épuisé.
SUSPECT_YEAR_MIN = 1950
SUSPECT_YEAR_MAX = 2025

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

# Initialiser le géocodeur
geolocator = Photon(user_agent="frontlet_fe_geocoder")
GEOCODER_RATE_LIMITED = False
LAST_GEOCODE_REQUEST_TS = 0.0
_GEOCODE_START_TIME = None
_GEOCODE_CALLS_AFTER_BUDGET = 0


def throttle_geocode_requests():
    """Respect a minimum delay between Nominatim requests to avoid 429."""
    global LAST_GEOCODE_REQUEST_TS
    now = time.time()
    elapsed = now - LAST_GEOCODE_REQUEST_TS
    if elapsed < GEOCODE_MIN_DELAY_SECONDS:
        # Petite pause volontaire pour rester dans un débit acceptable côté serveur.
        time.sleep(GEOCODE_MIN_DELAY_SECONDS - elapsed)
    LAST_GEOCODE_REQUEST_TS = time.time()


def geocode_single_query(query_text, timeout=10):
    """Run one geocoding query with throttling and 429 backoff retries."""
    global GEOCODER_RATE_LIMITED

    retries_429 = 0
    while retries_429 <= GEOCODE_MAX_429_RETRIES:
        try:
            throttle_geocode_requests()
            result = geolocator.geocode(query_text, timeout=timeout, language="en", limit=1)
            return result
        except GeocoderTimedOut:
            # Timeout réseau: laisser la boucle d'appel décider du retry global.
            raise
        except GeocoderServiceError as e:
            err = str(e)
            if "429" in err:
                retries_429 += 1
                if retries_429 > GEOCODE_MAX_429_RETRIES:
                    print("Rate limit Nominatim persistant (HTTP 429). Arrêt du géocodage en ligne pour cette exécution.")
                    GEOCODER_RATE_LIMITED = True
                    return None
                backoff = GEOCODE_429_BACKOFF_SECONDS * retries_429
                print(f"HTTP 429 reçu, pause backoff {backoff:.1f}s puis retry ({retries_429}/{GEOCODE_MAX_429_RETRIES})")
                time.sleep(backoff)
                continue
            # Erreur service non-429: la remonter au caller.
            raise
        except Exception as e:
            err = str(e)
            if "429" in err:
                retries_429 += 1
                if retries_429 > GEOCODE_MAX_429_RETRIES:
                    print("Rate limit Nominatim persistant (HTTP 429). Arrêt du géocodage en ligne pour cette exécution.")
                    GEOCODER_RATE_LIMITED = True
                    return None
                backoff = GEOCODE_429_BACKOFF_SECONDS * retries_429
                print(f"HTTP 429 reçu, pause backoff {backoff:.1f}s puis retry ({retries_429}/{GEOCODE_MAX_429_RETRIES})")
                time.sleep(backoff)
                continue
            raise

    return None

def geocode_location(location_name, max_retries=3):
    """
    Géocode un nom de lieu et retourne (latitude, longitude) ou (None, None).
    """
    if is_missing(location_name):
        return None, None

    global GEOCODER_RATE_LIMITED, _GEOCODE_START_TIME, _GEOCODE_CALLS_AFTER_BUDGET
    if GEOCODER_RATE_LIMITED:
        return None, None

    # Gestion budget temps
    if _GEOCODE_START_TIME is None:
        _GEOCODE_START_TIME = time.time()
    elapsed = time.time() - _GEOCODE_START_TIME
    if elapsed > GEOCODE_TIME_BUDGET_SEC:
        if _GEOCODE_CALLS_AFTER_BUDGET >= GEOCODE_MAX_AFTER_BUDGET:
            return None, None
        _GEOCODE_CALLS_AFTER_BUDGET += 1

    location_str = str(location_name).strip()

    for attempt in range(max_retries):
        try:
            location = geocode_single_query(location_str, timeout=10)
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
            err = str(e)
            if "429" in err:
                if not GEOCODER_RATE_LIMITED:
                    print("Rate limit Nominatim détecté (HTTP 429). Arrêt du géocodage en ligne pour cette exécution.")
                GEOCODER_RATE_LIMITED = True
                return None, None
            print(f"Erreur de géocodage pour {location_name}: {e}")
            return None, None
        except Exception as e:
            err = str(e)
            if "429" in err:
                if not GEOCODER_RATE_LIMITED:
                    print("Rate limit Nominatim détecté (HTTP 429). Arrêt du géocodage en ligne pour cette exécution.")
                GEOCODER_RATE_LIMITED = True
                return None, None
            print(f"Erreur inattendue lors du géocodage de {location_name}: {e}")
            return None, None
    
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
    
    # Hors limites (|lon| > 180 ou |lat| > 90)
    if abs(lon) > 180 or abs(lat) > 90:
        return True, "OUT_OF_BOUNDS"

    # Hors de la zone Europe / Méditerranée / Afrique du Nord / Proche-Orient
    # Bounding box : lat 10–72, lon –30 à 60
    if lat < 10 or lat > 72:
        return True, "OUT_OF_REGION_LAT"
    if lon < -30 or lon > 60:
        return True, "OUT_OF_REGION_LON"

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


def detect_transport_from_text(*values):
    """Detect a transport category from one or more text fragments."""
    text = " ".join(str(v) for v in values if not is_missing(v))
    if is_missing(text):
        return None

    txt = norm(text)
    transport_patterns = [
        ("boat", ["boat", "ship", "vessel", "ferry", "barca", "barcone", "peschereccio", "canoe", "raft", "dinghy"]),
        ("train", ["train", "rail", "railway", "locomotive"]),
        ("truck", ["truck", "lorry", "camion", "trailer"]),
        ("bus", ["bus", "coach", "autobus", "minibus"]),
        ("car", ["car", "auto", "automobile", "vehicle", "van"]),
        ("plane", ["plane", "aircraft", "flight", "airplane"]),
        ("motorbike", ["motorbike", "motorcycle", "scooter", "moto"]),
        ("bicycle", ["bicycle", "bike", "velo", "vélo"]),
        ("on_foot", ["on foot", "a piedi", "walk", "walking", "by foot"]),
    ]

    for token, keywords in transport_patterns:
        if any(keyword in txt for keyword in keywords):
            return token
    return None


CASUALTY_KEYWORDS_DEAD = [
    "morti", "morto", "morte", "mortes", "mort", "dead", "deaths", "killed", "ucciso", "uccisi",
    "annegato", "annegati", "drowned", "cadavere", "cadaveri", "corpo", "corpi", "vittime",
    "deceduto", "deceduti",
]
CASUALTY_KEYWORDS_INJURED = [
    "ferito", "feriti", "blessé", "blessés", "injured", "wounded",
]
CASUALTY_KEYWORDS_MISSING = [
    "disperso", "dispersi", "dispersa", "disperse", "missing", "scomparso", "scomparsi", "disappeared",
]
CASUALTY_KEYWORDS_SURVIVORS = [
    "superstite", "superstiti", "survivor", "survivors", "salvato", "salvati", "rescued", "soccorso", "soccorsi",
]
PERSON_NOUNS_PATTERN = (
    r"uomo|uomini|donna|donne|bambino|bambini|bambina|bambine|persona|persone|"
    r"passeggero|passeggeri|migrante|migranti|man|men|woman|women|child|children|"
    r"person|people|passenger|passengers"
)


def _parse_count_token(token):
    """Parse a numeric token written as digits only."""
    if token is None:
        return None
    raw_token = str(token)
    txt = norm(raw_token)
    txt = re.sub(r"[^0-9]", "", txt)
    if not txt:
        return None
    try:
        value = int(txt)
        # Les valeurs ressemblant a une annee ne sont pas des comptes de victimes dans ce contexte.
        # Conserver les milliers groupes comme 2.000 / 2,000 / 2 000 comme comptes valides.
        has_group_separator = re.search(r"\d[\.,\s]\d", raw_token) is not None
        if (not has_group_separator) and SUSPECT_YEAR_MIN <= value <= SUSPECT_YEAR_MAX:
            return None
        return value
    except Exception:
        return None


def _normalize_count_pair(first_num, second_num):
    """Convert captured numeric groups to a single integer (range -> upper bound)."""
    a = _parse_count_token(first_num)
    if a is None:
        return None
    if second_num is None or str(second_num).strip() == "":
        return a
    b = _parse_count_token(second_num)
    if b is None:
        return a
    return max(a, b)


def _extract_counts_for_keywords(text_norm, keywords):
    """Extract numeric counts around a keyword list using conservative context windows."""
    if not text_norm:
        return []

    kw_pattern = "|".join(re.escape(k) for k in keywords)
    # Examples matched:
    # - "9 morti"
    # - "morti 9"
    # - "dispersi tra 80 e 90"
    word_token = r"[A-Za-zÀ-ÖØ-öø-ÿ'’.-]+"
    num_token = r"(?:\d{1,3}(?:[\.,\s]\d{3})+|\d{1,4})"
    patterns = [
        rf"\b({num_token})(?:\s*(?:-|–|a|to|e|and)\s*({num_token}))?(?:\s+{word_token}){{0,2}}\s+(?:{kw_pattern})\b",
        rf"\b(?:{kw_pattern})\b(?:\s+{word_token}){{0,2}}\s+({num_token})(?:\s*(?:-|–|a|to|e|and)\s*({num_token}))?\b",
        rf"\b(?:{kw_pattern})\b[^\n\r\.;:]{{0,40}}?\b({num_token})\s*(?:-|–|a|to|e|and)\s*({num_token})\b",
        rf"\b(?:{kw_pattern})\b(?:\s+{word_token}){{0,8}}\s+(?:sono|eran[oa]|is|are|were)\s+({num_token})\b",
        rf"\b(?:{kw_pattern})\b(?:\s+{word_token}){{0,14}}\s+(?:sarebber[oa]|sono|eran[oa]|is|are|were)\s+(?:almeno|circa|about|environ|oltre|plus\s+de|more\s+than)?\s*({num_token})\b",
        rf"\b(?:altri|altre|other|autres)?\s*({num_token})\s+(?:{PERSON_NOUNS_PATTERN})\b(?:\s+{word_token}){{0,5}}\s+(?:{kw_pattern})\b",
        rf"\b(?:{kw_pattern})\b[^\n\r\.;:]{{0,80}}?\b(?:con|with|avec)\s+({num_token})\s+[a-zA-ZÀ-ÖØ-öø-ÿ'’.-]{{2,}}\b",
    ]

    values = []
    is_dead_group = set(keywords) == set(CASUALTY_KEYWORDS_DEAD)
    is_missing_group = set(keywords) == set(CASUALTY_KEYWORDS_MISSING)
    noise_re = r"\b(?:miglia|miles?|km|chilometri|metri|nm|nautiche|giorni?|ore|hours?|anni?|ans?)\b|\d+\s*enne\b"
    road_re = (
        r"\b(?:n|a|e|m|d|ss|sr|sp|dn|rn|us|i)\s*[-/]?\s*\d{1,4}\b"
        r"|\b(?:route|road|autoroute|autostrada|autovia|highway|motorway|strada|national|nationale|departementale|départementale)\b"
    )
    for pattern in patterns:
        for m in re.finditer(pattern, text_norm, flags=re.IGNORECASE):
            around_1 = ""
            around_2 = ""
            after_1 = ""
            after_2 = ""
            before_1 = ""
            before_2 = ""
            if m.lastindex and m.lastindex >= 1:
                s1, e1 = m.span(1)
                around_1 = text_norm[max(0, s1 - 16):min(len(text_norm), e1 + 16)]
                after_1 = text_norm[e1:min(len(text_norm), e1 + 24)]
                before_1 = text_norm[max(0, s1 - 28):s1]
            if m.lastindex and m.lastindex >= 2 and m.group(2):
                s2, e2 = m.span(2)
                around_2 = text_norm[max(0, s2 - 16):min(len(text_norm), e2 + 16)]
                after_2 = text_norm[e2:min(len(text_norm), e2 + 24)]
                before_2 = text_norm[max(0, s2 - 28):s2]

            if (around_1 and re.search(noise_re, around_1, flags=re.IGNORECASE)) or (
                around_2 and re.search(noise_re, around_2, flags=re.IGNORECASE)
            ):
                continue

            if (around_1 and re.search(road_re, around_1, flags=re.IGNORECASE)) or (
                around_2 and re.search(road_re, around_2, flags=re.IGNORECASE)
            ):
                continue

            # Ignore two-digit year shorthand in contexts like "del 97", "dall'inizio del 97".
            raw_1 = (m.group(1) or "").strip()
            raw_2 = (m.group(2) or "").strip() if m.lastindex and m.lastindex >= 2 else ""
            year_intro_re = r"(?:\b(?:dal|del|nel|since|depuis|desde|from)\s*['’]?\s*$|\b(?:dall|all)['’]?inizio\s+(?:del|dal)?\s*$|\binizio\s+(?:del|dal)?\s*$)"

            if re.fullmatch(r"\d{2}", raw_1) and before_1 and re.search(year_intro_re, before_1, flags=re.IGNORECASE):
                continue
            if raw_2 and re.fullmatch(r"\d{2}", raw_2) and before_2 and re.search(year_intro_re, before_2, flags=re.IGNORECASE):
                continue

            # Avoid counting the same number across categories when the immediate context
            # appartient clairement a un autre type de victime.
            if is_dead_group and (
                (after_1 and re.search(r"^\s*(?:dispers\w*|missing|scompar\w*|disappeared)\b", after_1, flags=re.IGNORECASE))
                or (after_2 and re.search(r"^\s*(?:dispers\w*|missing|scompar\w*|disappeared)\b", after_2, flags=re.IGNORECASE))
            ):
                continue

            if is_missing_group and (
                (after_1 and re.search(r"^\s*(?:mort\w*|dead|killed|annegat\w*|cadaver\w*|corpi?|vittim\w*|decedut\w*)\b", after_1, flags=re.IGNORECASE))
                or (after_2 and re.search(r"^\s*(?:mort\w*|dead|killed|annegat\w*|cadaver\w*|corpi?|vittim\w*|decedut\w*)\b", after_2, flags=re.IGNORECASE))
            ):
                continue

            val = _normalize_count_pair(m.group(1), m.group(2) if m.lastindex and m.lastindex >= 2 else None)
            if val is not None:
                values.append(val)

    return values


def _extract_people_list_count(text_norm):
    """
    Extract counts from explicit person lists near corpse/victim markers.
    Example: "i corpi di un bambino, un uomo e una donna" -> 3
    """
    if not text_norm:
        return 0

    list_markers = r"corpi?|cadaveri?|vittime"
    stop_markers = r"mort|deced|annegat|ferit|dispers|scompar|killed|dead|injured|missing|\.|;"
    pattern = rf"\b(?:{list_markers})\b\s+di\s+(?P<seg>.{{0,140}}?)(?:\b(?:{stop_markers})\b|$)"

    best = 0
    for m in re.finditer(pattern, text_norm, flags=re.IGNORECASE):
        seg = m.group("seg")
        if not seg:
            continue

        count = 0

        # Prefer explicit numeric mentions like "4 bambini" in victim lists.
        for ent in re.finditer(rf"\b(\d{{1,4}})\s+(?:{PERSON_NOUNS_PATTERN})\b", seg, flags=re.IGNORECASE):
            n = _parse_count_token(ent.group(1))
            if n is not None:
                count += n

        # Si aucune mention numerique n'est trouvee, compter les noms explicites de personnes listes.
        if count == 0:
            count = len(re.findall(rf"\b(?:{PERSON_NOUNS_PATTERN})\b", seg, flags=re.IGNORECASE))

        if count > best:
            best = count

    return best


def estimate_casualty_counts_from_text(text_value):
    """Estimate dead/injured/missing counts from narrative text."""
    if is_missing(text_value):
        return 1, 0, 0

    text_norm = norm(text_value)
    dead_vals = _extract_counts_for_keywords(text_norm, CASUALTY_KEYWORDS_DEAD)
    injured_vals = _extract_counts_for_keywords(text_norm, CASUALTY_KEYWORDS_INJURED)
    missing_vals = _extract_counts_for_keywords(text_norm, CASUALTY_KEYWORDS_MISSING)
    _ = _extract_counts_for_keywords(text_norm, CASUALTY_KEYWORDS_SURVIVORS)

    dead_count = max(dead_vals) if dead_vals else 0
    injured_count = max(injured_vals) if injured_vals else 0
    missing_count = max(missing_vals) if missing_vals else 0

    # Si dead et missing resolvent tous deux vers la meme valeur numerique unique,
    # treat it as one reported group to avoid accidental double counting.
    if dead_count > 0 and missing_count > 0 and dead_count == missing_count:
        merged_unique_counts = set(dead_vals) | set(missing_vals)
        if len(merged_unique_counts) == 1:
            missing_count = 0

    total_people = dead_count + injured_count + missing_count
    if total_people <= 0:
        people_list_count = _extract_people_list_count(text_norm)
        if people_list_count > 0:
            dead_count = people_list_count

    if (dead_count + injured_count + missing_count) <= 0:
        return 1, 0, 0
    return dead_count, injured_count, missing_count


COUNTRY_ALIASES = {
    "italia": "Italy",
    "francia": "France",
    "spagna": "Spain",
    "grecia": "Greece",
    "germania": "Germany",
    "portogallo": "Portugal",
    "croazia": "Croatia",
    "slovenia": "Slovenia",
    "slovacchia": "Slovakia",
    "svizzera": "Switzerland",
    "svezia": "Sweden",
    "olanda": "Netherlands",
    "regno unito": "United Kingdom",
    "inghilterra": "United Kingdom",
    "u.k.": "United Kingdom",
    "uk": "United Kingdom",
    "belgio": "Belgium",
    "danimarca": "Denmark",
    "egitto": "Egypt",
    "libia": "Libya",
    "siria": "Syria",
    "turchia": "Turkey",
    "tunisia": "Tunisia",
    "marocco": "Morocco",
    "capo verde": "Cape Verde",
    "cipro": "Cyprus",
    "comoro": "Comoros",
    "lituania": "Lithuania",
    "repubblica ceca": "Czechia",
    "ucraina": "Ukraine",
    "ungheria": "Hungary",
    "macedonia": "North Macedonia",
    "sahara occ.": "Western Sahara",
    "sahara occ": "Western Sahara",
    "sahara occidentale": "Western Sahara",
    "sahara": "Western Sahara",
    "jugoslavia": "Yugoslavia",
    "gran bretagna": "United Kingdom",
    "polonia": "Poland",
    "irlanda": "Ireland",
    "guinea bissau": "Guinea-Bissau",
}


def country_alias_key(value):
    """Normalize a value for COUNTRY_ALIASES matching."""
    return re.sub(r"[^a-z0-9 ]", "", norm(value)).strip()


COUNTRY_RECORD_LOOKUP = {}
for _c in pycountry.countries:
    for _nm in {
        getattr(_c, "name", None),
        getattr(_c, "official_name", None),
        getattr(_c, "common_name", None),
    }:
        if _nm:
            COUNTRY_RECORD_LOOKUP[country_alias_key(_nm)] = _c


def normalize_country_candidate(value):
    """Normalize common dataset country aliases to canonical English names."""
    if is_missing(value):
        return value
    key = country_alias_key(value)
    return COUNTRY_ALIASES.get(key, str(value).strip())


def resolve_country_record(country_code_or_name):
    """Resolve a country input to a pycountry record when possible."""
    if is_missing(country_code_or_name):
        return None

    val = normalize_country_candidate(country_code_or_name)
    val_key = country_alias_key(val)
    sval = re.sub(r'[^A-Za-z0-9]', '', str(val)).upper()

    if val_key in COUNTRY_RECORD_LOOKUP:
        return COUNTRY_RECORD_LOOKUP[val_key]

    try:
        if re.fullmatch(r'[A-Z]{2}', sval):
            return pycountry.countries.get(alpha_2=sval)
        if re.fullmatch(r'[A-Z]{3}', sval):
            return pycountry.countries.get(alpha_3=sval)
    except Exception:
        return None

    return None


def is_country_like_value(value):
    """Return True if the value appears to represent a country."""
    if is_missing(value):
        return False
    value_norm = country_alias_key(value)
    if value_norm in COUNTRY_ALIASES:
        return True
    if value_norm in COUNTRY_RECORD_LOOKUP:
        return True
    sval = re.sub(r'[^A-Za-z0-9]', '', str(value)).upper()
    if re.fullmatch(r'[A-Z]{2}', sval):
        return pycountry.countries.get(alpha_2=sval) is not None
    if re.fullmatch(r'[A-Z]{3}', sval):
        return pycountry.countries.get(alpha_3=sval) is not None
    return False

def extract_country_hint_from_lieu(lieu_value):
    """
    Extrait le nom de pays en anglais depuis la valeur brute de la colonne 'lieu'
    (gère les alias italiens via COUNTRY_ALIASES, ex. "Turchia" -> "Turkey").
    Retourne le nom anglais du pays, ou "" si non reconnu.
    """
    if is_missing(lieu_value):
        return ""
    cr = resolve_country_record(str(lieu_value).strip())
    if cr is not None:
        return getattr(cr, "name", "") or ""
    return ""


def ensure_country_node(g, country_code_or_name):
    """
    Try to find a country resource in graph by label or prefLabel or ISO code.
    Returns the country URIRef or None.
    """
    if is_missing(country_code_or_name):
        return None

    val = normalize_country_candidate(country_code_or_name)
    cc = resolve_country_record(val)

    if cc is not None:
        iso3 = getattr(cc, "alpha_3", None) or getattr(cc, "alpha_2", None)
        if not iso3:
            return None
        uri = DATA["fe_Country_" + iso3.upper()]
        if (uri, None, None) not in g:
            g.add((uri, RDF.type, F.Country))
            en_label = Literal(getattr(cc, "name", val), lang="en")
            if (uri, RDFS.label, en_label) not in g:
                g.add((uri, RDFS.label, en_label))
            g.add((uri, F.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            g.add((uri, F.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            g.add((uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return uri

    # IMPORTANT: ne créer un noeud Country que pour un pays réellement reconnu.
    return None

def create_age_node(g, age_value):
    """Create an Age node and return it."""
    if age_value is None or is_missing(age_value):
        return None
    try:
        age_num = int(float(str(age_value).strip()))
    except Exception:
        return None
    bn = BNode()
    g.add((bn, RDF.type, F.Age))
    g.add((bn, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    return bn

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
    Load optional CSV mapping: col1=fe_value, col2=Thesaurus_prefLabel
    Returns dict: normalized_fe_value -> normalized_thesaurus_label
    """
    mapping = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping
    try:
        mdf = pd.read_csv(mapping_path, sep=";", dtype=str)
        cols = list(mdf.columns)
        if len(cols) >= 2:
            fe_col = cols[0]
            thes_col = cols[1]
            for _, r in mdf.iterrows():
                a = norm(r.get(fe_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
            print(f"Loaded {len(mapping)} FE->Thesaurus mappings from CSV")
            print(f"Columns used: '{fe_col}' -> '{thes_col}'")
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


def clean_extracted_location(text):
    """Clean a raw location snippet extracted from free text."""
    if is_missing(text):
        return None

    value = str(text).strip(" \t\n\r,.;:-()[]{}\"'")
    value = re.split(r"[.;:]", value, maxsplit=1)[0].strip()
    value = re.split(
        r"\b(?:with|where|when|while|after|before|durante|mentre|con|alla deriva|sulla rotta|a bordo|in cui|nel quale|nella quale)\b",
        value,
        maxsplit=1,
        flags=re.IGNORECASE,
    )[0].strip()
    value = re.sub(r"^(?:le|la|il|lo|the)\s+", "", value, flags=re.IGNORECASE)
    value = re.sub(r"\s+", " ", value)

    if len(value) < 2 or len(value) > 80:
        return None
    if len(value.split()) > 10:
        return None

    return value


def is_plausible_place_name(value):
    """Keep only short, place-like chunks and reject narrative fragments."""
    if is_missing(value):
        return False

    txt = str(value).strip()
    if len(txt) < 2 or len(txt) > 80:
        return False

    bad_markers = {
        "morto", "morti", "cadavere", "cadaveri", "naufragio", "barca", "bordo",
        "imbarcazione", "migranti", "allarme", "lanciano", "ritrovata", "diretti",
        "sbarcato", "stenti", "dispersa", "collisione",
    }
    connector_words = {
        "di", "de", "del", "della", "delle", "dei", "da", "al", "alla", "du",
        "la", "le", "el", "los", "las", "d", "l",
        "a", "sul", "sulla", "sugli", "sulle", "sui", "degli", "e",
    }

    tokens = re.findall(r"[A-Za-z\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff''.-]+", txt)
    if not tokens or len(tokens) > 8:
        return False

    saw_upper_token = False
    for token in tokens:
        tnorm = norm(token)
        if tnorm in bad_markers:
            return False
        if token[0].isupper():
            saw_upper_token = True
        elif tnorm not in connector_words:
            return False

    return saw_upper_token


# Mots-clés narratifs non-géographiques utilisés pour couper les fragments extraits.
_LOC_NARRATIVE_CUT = re.compile(
    r"\b(?:con|alla\s+deriva|sulla\s+rotta|a\s+bordo|in\s+cui|nel\s+quale|nella\s+quale"
    r"|che\s+|il\s+quale|la\s+quale|dove\s|provoca|causa|viene|hanno|sono|si\s+trova"
    r"|with|where|when|while|after|before|during|durante|mentre)\b",
    re.IGNORECASE,
)

# Tokens d'arrêt : capitalisés mais non-géographiques.
_LOC_STOP_CAPS = {
    "I", "Il", "La", "Le", "Lo", "Gli", "Un", "Una", "Uno",
    "Si", "Ha", "Ho", "Che", "Da", "In", "Al", "Alla", "Del", "Della",
    "Nel", "Nella", "Dei", "Delle", "Sul", "Sulla", "Sugli", "Tra",
    "Con", "Per", "Ma", "Ed", "E", "O", "Non", "Secondo",
    "Soccorsa", "Bordo", "Cadaveri", "Passeggeri", "Morti", "Stenti",
    "Barca", "Deriva", "Rotta", "Largo", "Marina", "Militare",
    "Guardia", "Costiera", "Organizzazione",
}


def _clean_loc_fragment(raw: str):
    """
    Nettoie un fragment brut extrait par un pattern géographique :
    coupe à la première ponctuation forte ou mot narratif, supprime les articles initiaux.
    """
    if not raw:
        return None
    raw = raw.strip(" \t\n\r,.;:-()[]{}\"'")
    raw = re.split(r"[.;]", raw, maxsplit=1)[0].strip()
    raw = _LOC_NARRATIVE_CUT.split(raw, maxsplit=1)[0].strip(" \t\n\r,.;:-")
    # Couper avant article défini + nom commun (ex. "Melilla il corpo" → "Melilla")
    raw = re.split(r"\s+(?:il|la|lo|gli|i|un|una|uno|le|a|e|e')\s+[a-z\u00c0-\u00ff]", raw, maxsplit=1)[0].strip()
    raw = re.sub(r"^(?:l[ea]?|il|lo|gli|the|des?|l['\u2019])\s+", "", raw, flags=re.IGNORECASE)
    raw = re.sub(r"\s+", " ", raw).strip()
    if len(raw) < 2 or len(raw) > 80:
        return None
    return raw


def _first_proper_noun(raw: str):
    """Retourne le premier nom propre (token commençant par une majuscule) d'un fragment."""
    for token in re.findall(r"[A-Z\u00C0-\u00D6\u00D8-\u00DE][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{1,}", raw):
        if token not in _LOC_STOP_CAPS:
            return token
    return None


def _last_proper_noun(raw: str):
    """Retourne le dernier nom propre d'un fragment (utile pour 'X, Y' où Y est plus précis)."""
    result = None
    for token in re.findall(r"[A-Z\u00C0-\u00D6\u00D8-\u00DE][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{1,}", raw):
        if token not in _LOC_STOP_CAPS:
            result = token
    return result


def extract_location_from_text(text_value):
    """
    Extrait le lieu de mort le plus précis possible depuis le texte narratif.

    Hiérarchie décroissante de précision :
      1. Localité nommée  – « in località X », « nella località di X »
      2. Lieu nommé       – port, plage, rochers, enclave, frontière
      3. Ville / île      – « al largo di X », « nelle acque di X »,
                            « sull'isola di X », « a X [, nel distretto] »
      4. Province / district / région
      5. Fallback général – « vicino a X », « in X »

    Retourne la chaîne la plus précise trouvée, ou None.
    """
    if is_missing(text_value):
        return None
    text = str(text_value).strip()
    if not text:
        return None

    _P = re.IGNORECASE

    # ── Niveau 1 : localité nommée ───────────────────────────────────────────
    for pat in [
        r"\bin\s+localit[\u00e0a]\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bnell[ae]\s+localit[\u00e0a]\s+(?:di\s+)?(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bnella\s+localit[\u00e0a]\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bin\s+loc(?:\.|alita)?\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
    ]:
        m = re.search(pat, text, _P)
        if m:
            raw = _clean_loc_fragment(m.group("loc"))
            if raw:
                # Couper sur la virgule OU sur " e " (ex. "Vagia e Skylomantra" → "Vagia")
                result = re.split(r",|\s+e\s+", raw)[0].strip()
                if len(result) >= 2:
                    return result

    # ── Niveau 2 : lieu nommé (port, plage, rochers, enclave, frontière) ────
    for pat in [
        r"\bnell[ae]\s+acque\s+del\s+porto\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bnel\s+porto\s+(?:dell['\u2019ae]\s+\S+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bporto\s+d[i'\u2019]\s*(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bsulle?\s+spiagge?\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bsulla\s+spiaggia\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bsugli\s+scogli\s+(?:di\s+|dell['\u2019ae]\s+(?:isola\s+di\s+)?)?(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bscogli\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\benclave\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\bconfine\s+(?:tra\s+[A-Z]\S+\s+e\s+la\s+|con\s+la\s+)(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
        r"\b(?:nel\s+Canale\s+di|nello\s+Stretto\s+di)\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{1,50})",
    ]:
        m = re.search(pat, text, _P)
        if m:
            raw = _clean_loc_fragment(m.group("loc"))
            if raw:
                result = raw.split(",")[0].strip()
                if len(result) >= 2:
                    return result

    # ── Niveau 3 : ville / île ───────────────────────────────────────────────
    _lvl3_patterns = [
        # "a X, nel distretto/provincia di Y" → X est la ville
        (False, r"\b(?:a|ad)\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})\s*,\s*(?:nel|nella)\s+(?:distretto|provincia)"),
        # "nelle acque di X, nel distretto de Y" → X est la ville
        (False, r"\bnell[ae]\s+acque\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})\s*,"),
        # "davanti alla/alle costa/coste (turca/…) di X"
        (False, r"\bdavanti\s+all[ae]\s+cost[ae]\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})"),
        # "sulle coste (turche/…) di X"
        (False, r"\bsulle?\s+coste?\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})"),
        # "nelle acque di X"
        (False, r"\bnell[ae]\s+acque\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})"),
        # "al largo di X, Y" – virgule possible ; Y peut être plus précis
        (True,  r"\bal\s+largo\s+(?:dell['\u2019ae]\s+isola\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''., \s-]{2,60})"),
        # "al largo dell'isola X" (sans "di")
        (False, r"\bal\s+largo\s+dell['\u2019]isola\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})\b"),
        # "a nord/sud/est/ovest di X"
        (False, r"\ba\s+(?:nord|sud|est|ovest|nord-est|nord-ovest|sud-est|sud-ovest)\s+(?:di\s+)?(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})"),
        # "sull'isola (greca/…) di X"
        (False, r"\bsull['\u2019]isola\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})"),
        (False, r"\ball['\u2019]isola\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})"),
        (False, r"\bisola\s+(?:\w+\s+)?di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})"),
        (False, r"\bsull['\u2019]isola\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})\b"),
        # "tra le localita di X e Y" → X
        (False, r"\btra\s+le\s+localit[\u00e0a]\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})"),
        # "a X" général (ville)
        (False, r"\b(?:a|ad)\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40}(?:\s+[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40}){0,2})\b"),
    ]
    for is_al_largo, pat in _lvl3_patterns:
        m = re.search(pat, text, _P)
        if m:
            raw = _clean_loc_fragment(m.group("loc"))
            if not raw:
                continue
            # Pour "al largo di X, Y" : Y (après la virgule) est souvent la ville
            if is_al_largo and "," in raw:
                parts = [p.strip() for p in raw.split(",") if p.strip()]
                candidate = _last_proper_noun(parts[-1]) if parts else None
                if candidate:
                    return candidate
                raw = parts[0]
            # Fragment trop long → extraire le premier nom propre
            if len(raw.split()) > 4:
                pn = _first_proper_noun(raw)
                if pn:
                    raw = pn
            if raw and len(raw) >= 2:
                return raw

    # ── Niveau 4 : province / district / région ──────────────────────────────
    for pat in [
        r"\bnell[ae]?\s+(?:provincia|distretto|dipartimento)\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})",
        r"\bnella\s+regione\s+(?:di\s+)?(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})",
        r"\b(?:nel\s+)?distretto\s+di\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''.-]{2,40})",
    ]:
        m = re.search(pat, text, _P)
        if m:
            raw = _clean_loc_fragment(m.group("loc"))
            if raw:
                result = raw.split(",")[0].strip()
                if len(result) >= 2:
                    return result

    # ── Niveau 5 : fallback général ───────────────────────────────────────────
    for pat in [
        r"\b(?:vicino\s+a|nei\s+pressi\s+di|in\s+prossimit[\u00e0a]\s+(?:di\s+)?|near|close\s+to)\s+(?P<loc>[A-Z][A-Za-z\u00C0-\u00F6\u00F8-\u00FF''. \s-]{2,50})",
        r"\b(?:in|at)\s+(?P<loc>[A-Z][^,.;:()]{2,60})",
        r"\b(?:rotta\s+per|route\s+to|heading\s+to|diretti\s+a|diretto\s+a|en\s+route\s+to)\s+(?P<loc>[^,.;:()]{2,60})",
    ]:
        m = re.search(pat, text, _P)
        if m:
            raw = _clean_loc_fragment(m.group("loc"))
            if raw and is_plausible_place_name(raw):
                return raw

    return None

def normalize_location_choice(value):
    """Normalize a raw location candidate into a concise place-like name."""
    if is_missing(value):
        return ""

    raw = str(value).strip()
    if not raw:
        return ""

    if is_plausible_place_name(raw) and len(raw) <= 80:
        return raw

    extracted = extract_location_from_text(raw)
    if extracted and is_plausible_place_name(extracted):
        return extracted

    cleaned = clean_extracted_location(raw)
    if cleaned and is_plausible_place_name(cleaned):
        return cleaned

    caps = re.findall(r"[A-Z][A-Za-zÀ-ÖØ-öø-ÿ'’.-]{2,}", raw)
    stop_caps = {
        "Soccorsa", "Bordo", "Cadaveri", "Passeggeri", "Morti", "Stenti", "Barca", "Deriva",
        "Rotta", "Largo", "Al", "A", "Un", "Una", "Alla", "Dalla", "Sulla",
    }
    caps = [c for c in caps if c not in stop_caps]
    if caps:
        return caps[-1]

    return raw[:80]


def slugify_location_name(value, default="unknown"):
    """Create a stable ASCII slug from a location name."""
    if is_missing(value):
        return default
    txt = unicodedata.normalize("NFKD", str(value)).encode("ascii", "ignore").decode("ascii")
    slug = re.sub(r"[^a-zA-Z0-9]+", "_", txt).strip("_").lower()
    return slug or default


def load_persistent_geocode_cache(cache_path=GEOCODE_CACHE_PATH):
    """Load geocoding cache from disk: {cache_key: [lat, lon]}.
    Les entrées sans séparateur '||' (ancien format sans pays) sont ignorées
    pour forcer un nouveau géocodage contextualisé par pays."""
    if not os.path.exists(cache_path):
        return {}
    try:
        with open(cache_path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        cache = {}
        skipped = 0
        for key, value in data.items():
            # Ignorer les entrées de l'ancien format (sans contexte pays)
            if "||" not in str(key):
                skipped += 1
                continue
            if isinstance(value, list) and len(value) == 2:
                lat, lon = value
                if lat is not None and lon is not None:
                    cache[str(key)] = (float(lat), float(lon))
        print(f"Cache géocodage chargé: {len(cache)} lieux ({skipped} entrées obsolètes ignorées)")
        return cache
    except Exception as e:
        print(f"Warning: cache géocodage illisible ({cache_path}): {e}")
        return {}


def save_persistent_geocode_cache(cache, cache_path=GEOCODE_CACHE_PATH):
    """Save geocoding cache to disk."""
    try:
        os.makedirs(os.path.dirname(cache_path), exist_ok=True)
        payload = {k: [v[0], v[1]] for k, v in cache.items() if isinstance(v, tuple) and len(v) == 2 and v[0] is not None and v[1] is not None}
        with open(cache_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=2)
        print(f"Cache géocodage sauvegardé: {len(payload)} lieux")
    except Exception as e:
        print(f"Warning: impossible de sauvegarder le cache géocodage: {e}")


def add_or_update_geometry(g, event_uri, geometry_uri, location_label=None, lat=None, lon=None, is_geocoded=False):
    """Create a geometry node, keep a human label, and add WKT when coordinates are available."""
    if lat is None or lon is None:
        return False

    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return False

    if not (math.isfinite(lat_f) and math.isfinite(lon_f)):
        return False

    is_suspicious, _ = is_suspicious_coordinate(lat_f, lon_f)
    if is_suspicious:
        return False

    g.add((event_uri, GEO.hasGeometry, geometry_uri))
    g.add((geometry_uri, RDF.type, GEO.Geometry))
    if not is_missing(location_label):
        g.add((geometry_uri, RDFS.label, Literal(str(location_label).strip())))

    wkt = build_wkt_for_location_precision(location_label or "", lat_f, lon_f, bool(is_geocoded))
    g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
    g.add((geometry_uri, F.hasPrecision, Literal(not is_geocoded, datatype=XSD.boolean)))
    return True

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

# Géocodage activé sur toutes les lignes (résultats mis en cache JSON).
geocode_row_indices = set(df.index)
print(f"Géocodage activé sur {n_rows} lignes (toutes lignes, cache JSON actif)")
print(
    "Paramètres anti-429: "
    f"min_delay={GEOCODE_MIN_DELAY_SECONDS}s, "
    f"backoff={GEOCODE_429_BACKOFF_SECONDS}s, "
    f"max_429_retries={GEOCODE_MAX_429_RETRIES}, "
    f"budget={GEOCODE_TIME_BUDGET_SEC}s"
)

# ------------------- Cache de geocodage ------------------
def make_geocode_cache_key(location_value, country_hint):
    """Clé de cache stable : 'lieu||Pays' quand le pays est connu, sinon 'lieu'."""
    if country_hint:
        return f"{location_value}||{country_hint}"
    return location_value


def build_geocode_cache(values, label="lieux", persistent_cache=None, country_hint_map=None):
    """
    Géocode chaque valeur unique et retourne {cache_key: (lat, lon)}.
    country_hint_map : dict optionnel {location_value: country_english_name}.
      - La clé de cache devient "loc||Pays" quand le pays est connu.
      - La requête Photon est enrichie en "loc, Pays" pour forcer la bonne région.
    """
    cache = {}
    if persistent_cache is None:
        persistent_cache = {}
    if country_hint_map is None:
        country_hint_map = {}

    # Construire l'ensemble unique (valeur, hint_pays)
    unique_pairs = sorted({
        (str(v).strip(), country_hint_map.get(str(v).strip(), ""))
        for v in values
        if not is_missing(v) and str(v).strip()
    })
    total = len(unique_pairs)

    if total == 0:
        return cache

    hits = sum(
        1 for val, hint in unique_pairs
        if make_geocode_cache_key(val, hint) in persistent_cache
    )
    print(f"Pré-géocodage: {total} {label} uniques (cache hit={hits}, online={total-hits})")
    budget_start = time.time()
    budget_exceeded = False
    calls_after_budget = 0
    for i, (value, country_hint) in enumerate(unique_pairs, start=1):
        cache_key = make_geocode_cache_key(value, country_hint)
        if cache_key in persistent_cache:
            cache[cache_key] = persistent_cache[cache_key]
            continue
        if GEOCODER_RATE_LIMITED:
            print(f"  Pré-géocodage {label}: interrompu à {i-1}/{total} (rate limit)")
            break
        if not budget_exceeded and (time.time() - budget_start) > GEOCODE_TIME_BUDGET_SEC:
            budget_exceeded = True
            print(f"  Budget temps écoulé ({GEOCODE_TIME_BUDGET_SEC}s) après {i-1} appels. Encore {GEOCODE_MAX_AFTER_BUDGET} appels online autorisés.")
        if budget_exceeded:
            calls_after_budget += 1
            if calls_after_budget > GEOCODE_MAX_AFTER_BUDGET:
                print(f"  Limite post-budget atteinte ({GEOCODE_MAX_AFTER_BUDGET}). Arrêt géocodage en ligne.")
                break
        # Requête enrichie avec le contexte pays pour plus de précision
        query = f"{value}, {country_hint}" if country_hint else value
        if country_hint:
            print(f"  Géocodage «{value}» dans le contexte pays: {country_hint}")
        coords = geocode_location(query)
        cache[cache_key] = coords
        if coords[0] is not None and coords[1] is not None:
            persistent_cache[cache_key] = coords
        if i % 50 == 0 or i == total:
            print(f"  Pré-géocodage {label}: {i}/{total}")

    return cache


def is_geocodable_location_text(value):
    """Heuristic filter to avoid geocoding obvious non-location texts."""
    if is_missing(value):
        return False
    txt = str(value).strip()
    if len(txt) > 80:
        return False
    txt_norm = norm(txt)
    if any(marker in txt_norm for marker in ["oceano", "ocean", "atlantico", "mediterranean", "mediterraneo", "sea"]):
        return False
    if is_country_like_value(txt):
        return False
    # Ne conserver que les lieux de granularite locale pour les points geometriques.
    broad_localities = {"istanbul"}
    if norm(txt) in broad_localities:
        return False
    return True


# Préparer les listes de valeurs à géocoder.
persistent_geocode_cache = load_persistent_geocode_cache()
rows_needing_lieu_geocode = []
rows_needing_inhumation_geocode = []
row_location_choice = {}
row_country_hint = {}  # idx -> nom de pays en anglais extrait depuis "lieu"

count_location_from_text = 0
count_location_from_lieu = 0
count_location_missing = 0

for prep_idx, prep_row in df.iterrows():
    text_prep = prep_row.get("text", "")
    lieu_prep = prep_row.get("lieu", "") or prep_row.get("lieu".lower(), "")

    # Extraire le pays depuis la colonne "lieu" pour contraindre le géocodage
    country_hint = extract_country_hint_from_lieu(lieu_prep)
    row_country_hint[prep_idx] = country_hint

    text_location = extract_location_from_text(text_prep)
    if not is_missing(text_location):
        location_choice = normalize_location_choice(text_location)
        count_location_from_text += 1
    elif not is_missing(lieu_prep):
        location_choice = normalize_location_choice(lieu_prep)
        count_location_from_lieu += 1
    else:
        location_choice = ""
        count_location_missing += 1

    if not is_geocodable_location_text(location_choice):
        location_choice = ""
    row_location_choice[prep_idx] = location_choice

    if is_geocodable_location_text(location_choice):
        rows_needing_lieu_geocode.append(location_choice)

    comm_enterrement_prep = prep_row.get("Comm_enterrement", "")
    if is_geocodable_location_text(comm_enterrement_prep):
        rows_needing_inhumation_geocode.append(str(comm_enterrement_prep).strip())

# Construire loc_to_country_hint : {location_choice -> pays en anglais}
# Si une même valeur de lieu apparaît pour plusieurs pays, on prend la valeur
# non-vide la plus fréquente (la première rencontrée suffit ici).
loc_to_country_hint: dict[str, str] = {}
for _pidx, _loc in row_location_choice.items():
    if _loc:
        _hint = row_country_hint.get(_pidx, "")
        if _hint and _loc not in loc_to_country_hint:
            loc_to_country_hint[_loc] = _hint

geocode_cache_lieu = build_geocode_cache(
    rows_needing_lieu_geocode,
    label="lieux de décès",
    persistent_cache=persistent_geocode_cache,
    country_hint_map=loc_to_country_hint,
)
geocode_cache_inhumation = build_geocode_cache(rows_needing_inhumation_geocode, label="lieux d'inhumation", persistent_cache=persistent_geocode_cache)

# Build cemetery geocode cache: pour les communes d'enterrement sans coordonnées,
# chercher spécifiquement les cimetières plutôt que juste la commune.
# Créer un map commune -> pays pour les cimetières
cemetery_country_hint_map = {}
for _pidx, _comm in enumerate(rows_needing_inhumation_geocode):
    if _comm and _pidx in row_country_hint:
        cemetery_country_hint_map[_comm] = row_country_hint[_pidx]

geocode_cache_cemetery = build_cemetery_geocode_cache(
    rows_needing_inhumation_geocode,
    geocoder=geolocator,
    country_hint_map=cemetery_country_hint_map if cemetery_country_hint_map else None,
)

save_persistent_geocode_cache(persistent_geocode_cache)
print(
    "Détection de lieu (toutes lignes): "
    f"depuis text={count_location_from_text}, "
    f"fallback lieu={count_location_from_lieu}, "
    f"sans lieu={count_location_missing}"
)

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or F.Injury
MISSING_EVENT_CLASS = F.Missing
EMBARK_EVENT_CLASS = find_by_label(g_ref, "Embark") or F.EmbarkEvent or F.Event
DEATH_CERTIFICATE_CLASS = find_by_label(g_ref, "DeathCertificate") or F.DeathCertificate
SOURCE_CLASS = find_by_label(g_ref, "Source") or F.Source

if (MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_EVENT_CLASS, RDFS.subClassOf, F.IndividualEvent))
    if (MISSING_EVENT_CLASS, RDFS.label, None) not in g:
        g.add((MISSING_EVENT_CLASS, RDFS.label, Literal("Missing", lang="en")))

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
count_injury_events = 0
count_missing_events = 0
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
count_geometry_nodes = 0
count_geometry_with_wkt = 0
count_rows_multi_people = 0
count_additional_typed_events = 0

for idx, row in df.iterrows():
    dead_count, injury_count, missing_count = estimate_casualty_counts_from_text(row.get("text", ""))
    primary_people_count = dead_count + missing_count
    if injury_count > 0 and primary_people_count == 0:
        # Une blessure ne constitue pas un resultat final; on cree au minimum une disparition d'ancrage.
        missing_count = 1
        primary_people_count = 1

    # Une blessure est ante-mortem/ante-disparition: on ne cree pas plus de blessures que d'evenements primaires.
    injury_event_count = min(injury_count, primary_people_count) if primary_people_count > 0 else 0

    # Le nombre de personnes impliquees correspond aux personnes ayant un resultat final (Death ou Missing).
    people_involved_for_row = primary_people_count

    if people_involved_for_row >= 2:
        count_rows_multi_people += 1

    repatriation_event_uri = None
    collective_event_uri = None
    if people_involved_for_row >= 2:
        collective_event_uri = DATA[f"CollectiveEvent_row_{idx+1}"]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1
            recit_val = row.get("Recit_passage_deces", "") or row.get("recit_passage_deces", "")
            if recit_val and not is_missing(recit_val):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(recit_val).strip())))
            elif not is_missing(row.get("text", "")):
                g.add((collective_event_uri, PROP_hasNarrative, Literal(str(row.get("text", "")).strip())))

    event_specs = []
    for i in range(dead_count):
        event_specs.append((DEATH_EVENT_CLASS, "Death", i + 1))
    for i in range(missing_count):
        event_specs.append((MISSING_EVENT_CLASS, "Missing", i + 1))

    person_event_pairs = []
    injury_event_pairs = []
    primary_event_uris = []
    for pair_idx, (event_class_uri, event_kind, type_index) in enumerate(event_specs, start=1):
        person_uri = DATA[f"fe_Person_{idx+1}_{pair_idx}"]
        # Les URI de deces utilisent un motif explicite; les autres evenements gardent les IDs historiques.
        if event_kind == "Death":
            event_uri = DATA[f"fe_Death_{idx+1}_{type_index}"]
        else:
            event_uri = DATA[f"fe_{event_kind}_gen_{idx+1}_{type_index}"]

        g.add((person_uri, RDF.type, PERSON_CLASS))
        g.add((event_uri, RDF.type, event_class_uri))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))

        count_person += 1
        if event_kind == "Death":
            count_death_events += 1
            primary_event_uris.append(event_uri)
        elif event_kind == "Missing":
            count_missing_events += 1
            primary_event_uris.append(event_uri)

        person_event_pairs.append((person_uri, event_uri))

    # Les blessures sont des evenements additionnels rattaches aux personnes ayant un resultat final.
    if person_event_pairs and injury_event_count > 0:
        for injury_idx in range(1, injury_event_count + 1):
            anchor_person_uri, anchor_event_uri = person_event_pairs[(injury_idx - 1) % len(person_event_pairs)]
            injury_event_uri = DATA[f"fe_Injury_gen_{idx+1}_{injury_idx}"]
            g.add((injury_event_uri, RDF.type, INJURY_EVENT_CLASS))
            g.add((injury_event_uri, RDF.type, F.IndividualEvent))
            g.add((anchor_person_uri, PROP_composedOf, injury_event_uri))
            g.add((injury_event_uri, PROP_temporal_before, anchor_event_uri))
            g.add((anchor_event_uri, PROP_temporal_after, injury_event_uri))
            if collective_event_uri is not None:
                g.add((injury_event_uri, F.group, collective_event_uri))
            injury_event_pairs.append((anchor_person_uri, injury_event_uri))
            count_injury_events += 1

    all_event_pairs = person_event_pairs + injury_event_pairs

    # NOMS
    val = row.get("Nom_connu", "")
    if val and not is_missing(val):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_hasName, Literal(str(val).strip())))

    val = row.get("Nom_non_public", "")
    if val and not is_missing(val):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_hasOfficialName, Literal(str(val).strip())))

    val = row.get("Autre_nom", "")
    if val and not is_missing(val):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_otherName, Literal(str(val).strip())))

    # AGE
    age_val = row.get("Age", "")
    try:
        if age_val is not None and age_val != "" and not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
            for person_uri, _ in person_event_pairs:
                age_node = create_age_node(g, age_val)
                if age_node:
                    g.add((person_uri, PROP_hasAgeLink, age_node))
                    # Also add direct hasAge for convenience
                    for age_v in g.objects(age_node, F.hasAge):
                        g.add((person_uri, F.hasAge, age_v))
    except Exception:
        pass

    # SEXE (inference textuelle depuis les récits)
    sexe = norm(row.get("text", "") or row.get("NOTA", "") or row.get("Description", ""))
    if sexe and not is_missing(sexe):
        for person_uri, _ in person_event_pairs:
            if any(k in sexe for k in (" hombre ", "hombre", " varon", "varón", " male ", " man ", " boy ", " nino", "niño")):
                if THES_male is not None:
                    g.add((person_uri, F.hasGender, THES_male))
                else:
                    g.add((person_uri, F.hasGender, Literal("male")))
            elif any(k in sexe for k in (" mujer ", "mujer", " female ", " woman ", " girl ", " nina", "niña")):
                if THES_female is not None:
                    g.add((person_uri, F.hasGender, THES_female))
                else:
                    g.add((person_uri, F.hasGender, Literal("female")))

    # LIEU DE NAISSANCE
    birth_country = None
    if not is_missing(row.get("Pays_naissance", "")):
        birth_country = ensure_country_node(g, row.get("Pays_naissance"))
    elif not is_missing(row.get("Nati", "")):
        birth_country = ensure_country_node(g, row.get("Nati"))
    if birth_country:
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES
    comment_cdb = row.get("text", "")
    if comment_cdb and not is_missing(comment_cdb):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))

    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["text", "Cause_deces", "lieu", "Pays_naissance"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Comm_enterrement", "Enterrement", "source", "url2"], is_missing))

    # DATE DE DÉCÈS (Date_mort)
    date_mort_val = row.get("data", "") or row.get("data", "")
    parsed_date = None
    if date_mort_val and not is_missing(date_mort_val):
        try:
            date_str = str(date_mort_val).strip()
            try:
                parsed_date = datetime.strptime(date_str, "%Y-%m-%d")
            except ValueError:
                pass
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str.split()[0], "%Y-%m-%d")
                except (ValueError, IndexError):
                    pass
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str, "%d/%m/%Y")
                except ValueError:
                    pass
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str, "%d-%m-%Y")
                except ValueError:
                    pass
            if parsed_date:
                date_iso = parsed_date.strftime("%Y-%m-%d")
                weekday_name = infer_day_of_week_name(date_iso, date_str, row.get("text", ""))
                for _, event_uri in all_event_pairs:
                    g.add((event_uri, TIME.inXSDDate, Literal(date_iso, datatype=XSD.date)))
                    if weekday_name:
                        g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                        g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                        g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
        except Exception as e:
            print(f"Erreur parsing date pour ligne {idx+1}: {date_mort_val} - {e}")

    # Repli sur le jour de la semaine depuis le texte libre (ex. "domenica") meme si le parsing de date echoue.
    if parsed_date is None:
        weekday_name = infer_day_of_week_name(date_mort_val, row.get("text", ""), row.get("Cause_deces", ""))
        if weekday_name:
            for _, event_uri in all_event_pairs:
                g.add((event_uri, TIME.dayOfWeek, TIME[weekday_name]))
                g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))

    # CAUSE DE DÉCÈS
    cause_deces_val = row.get("Cause_deces", "") or row.get("cause_deces", "")
    if cause_deces_val and not is_missing(cause_deces_val):
        uri, lbl, is_literal = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        for _, event_uri in person_event_pairs:
            if uri:
                g.add((event_uri, PROP_hasDeathCause, uri))
            elif lbl:
                g.add((event_uri, PROP_hasDeathCause, Literal(lbl)))

        if uri:
            count_cause_matched += len(person_event_pairs)
        elif lbl:
            count_cause_literal += len(person_event_pairs)

        is_accident, transport_type = detect_traffic_accident_and_transport(cause_deces_val)
        if is_accident:
            count_traffic_accidents += 1
            if transport_type:
                count_transport_identified += 1

    # CERTIFICAT DE DÉCÈS
    acte_deces_val = row.get("Acte_deces", "") or row.get("acte_deces", "")
    if acte_deces_val and not is_missing(acte_deces_val):
        for pair_idx, (_, event_uri) in enumerate(person_event_pairs, start=1):
            certificate_uri = DATA[f"DeathCertificate_{idx+1}_{pair_idx}"]
            g.add((certificate_uri, RDF.type, DEATH_CERTIFICATE_CLASS))
            g.add((event_uri, PROP_certificate, certificate_uri))
            g.add((certificate_uri, PROP_hasIdCertificate, Literal(str(acte_deces_val).strip())))
            count_death_certificates += 1

    # frontiere_EX -> borderOUT
    front_ex = row.get("Frontiere_EX", "") or row.get("frontiere_EX", "") or row.get("frontiere_EX".lower(), "")
    if not is_missing(front_ex):
        cnode = ensure_country_node(g, str(front_ex).strip())
        if cnode:
            for _, event_uri in all_event_pairs:
                g.add((event_uri, PROP_borderOUT, cnode))

    # frontiere_IN -> borderIN
    front_in = row.get("Frontiere_IN", "") or row.get("frontiere_IN", "") or row.get("frontiere_IN".lower(), "")
    if not is_missing(front_in):
        cnode = ensure_country_node(g, str(front_in).strip())
        if cnode:
            for _, event_uri in all_event_pairs:
                g.add((event_uri, PROP_borderIN, cnode))

    raw_lieu_val = row.get("lieu", "") or row.get("lieu".lower(), "")
    lieu_val = row_location_choice.get(idx, "")

    # GEO
    lat = row.get("Coord_Lat_deces", "") or row.get("Coord_lat_deces", "")
    lon = row.get("Coord_Long_deces", "") or row.get("Coord_long_deces", "")
    lat_f = None
    lon_f = None
    try:
        if not is_missing(lat) and not is_missing(lon):
            lat_candidate = float(lat)
            lon_candidate = float(lon)
            if math.isfinite(lat_candidate) and math.isfinite(lon_candidate):
                is_suspicious, reason = is_suspicious_coordinate(lat_candidate, lon_candidate)
                if is_suspicious:
                    print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon_candidate}, {lat_candidate}")
                else:
                    lat_f = lat_candidate
                    lon_f = lon_candidate
    except Exception:
        lat_f = None
        lon_f = None

    is_geocoded_from_lieu = False
    if lat_f is None or lon_f is None:
        if not is_missing(lieu_val):
            try:
                country_hint_for_row = row_country_hint.get(idx, "")
                cache_key_lieu = make_geocode_cache_key(str(lieu_val).strip(), country_hint_for_row)
                lat_lieu, lon_lieu = geocode_cache_lieu.get(cache_key_lieu, (None, None))
                if lat_lieu is not None and lon_lieu is not None and math.isfinite(lat_lieu) and math.isfinite(lon_lieu):
                    is_suspicious, reason = is_suspicious_coordinate(lat_lieu, lon_lieu)
                    if is_suspicious:
                        print(f"  ⚠️  Coordonnée suspecte ignorée pour lieu ({reason}): {lon_lieu}, {lat_lieu}")
                    else:
                        lat_f = lat_lieu
                        lon_f = lon_lieu
                        is_geocoded_from_lieu = True
            except Exception as e:
                print(f"Erreur géocodage lieu pour ligne {idx+1}: {lieu_val} - {e}")

    for pair_idx, (_, event_uri) in enumerate(all_event_pairs, start=1):
        if not is_missing(lieu_val):
            geometry_slug = slugify_location_name(lieu_val)
            geometry_uri = DATA[f"fe_geometry_{geometry_slug}_{idx+1}_{pair_idx}"]
            if add_or_update_geometry(
                g,
                event_uri,
                geometry_uri,
                location_label=lieu_val,
                lat=lat_f,
                lon=lon_f,
                        is_geocoded=False,
            ):
                count_geometry_with_wkt += 1
            count_geometry_nodes += 1

            g.add((event_uri, F.lieu, Literal(str(lieu_val).strip())))

    # TRANSPORT
    transport_val = row.get("transport", "") or row.get("Transport", "") or row.get("transport".lower(), "")
    if is_missing(transport_val):
        transport_val = detect_transport_from_text(row.get("Cause_deces", ""), row.get("text", ""), row.get("lieu", ""))
    if not is_missing(transport_val):
        t_norm = norm(transport_val)
        is_human_transport = any(keyword in t_norm for keyword in ["marche", "nage", "pied", "humain"])

        if is_human_transport:
            if THES_human is not None:
                for _, event_uri in person_event_pairs:
                    g.add((event_uri, F.transportMode, THES_human))
        else:
            th_term = find_thesaurus_term_by_prefLabel_fr(g_ref, transport_val)
            if th_term is None:
                for s, p, o in g_ref.triples((None, SKOS.prefLabel, None)):
                    if norm(o).find(norm(transport_val)) >= 0:
                        th_term = s
                        break
                if th_term is None:
                    for s, p, o in g_ref.triples((None, RDFS.label, None)):
                        if norm(o).find(norm(transport_val)) >= 0:
                            th_term = s
                            break
            slug = re.sub(r'[^a-z0-9_]', '_', norm(transport_val))
            if slug and slug not in ("nan", "none", ""):
                transport_uri = DATA["fe_Transport_" + slug + "_" + str(idx+1)]
                if str(transport_uri) not in created_transports:
                    g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
                    if th_term is not None:
                        g.add((transport_uri, RDF.type, th_term))
                    g.add((transport_uri, RDFS.label, Literal(str(transport_val).strip())))
                    created_transports[str(transport_uri)] = transport_uri
                    count_transports += 1

                for pair_idx, (person_uri, event_uri) in enumerate(person_event_pairs, start=1):
                    g.add((event_uri, PROP_transportType, transport_uri))
                    # Lien direct Transport -> usedIn -> Death/Missing
                    g.add((transport_uri, PROP_usedIn, event_uri))
                    embark_uri = DATA[f"EmbarkEvent_{idx+1}_{slug}_{pair_idx}"]
                    if (embark_uri, None, None) not in g:
                        g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                    g.add((embark_uri, PROP_usedIn, transport_uri))
                    # Lien bidirectionnel pour consistence
                    g.add((transport_uri, PROP_usedIn, embark_uri))
                    g.add((embark_uri, PROP_temporal_before, event_uri))
                    g.add((event_uri, PROP_temporal_after, embark_uri))
                    g.add((person_uri, PROP_composedOf, embark_uri))
                    count_embark += 1

    # RAPATRIEMENT
    enterrement_text = str(row.get("Enterrement", "")).strip()
    if ("rapatrié" in norm(enterrement_text) or "rapatriement" in norm(enterrement_text)) and "?" not in enterrement_text:
        for pair_idx, (person_uri, event_uri) in enumerate(person_event_pairs, start=1):
            repatriation_event_uri = DATA[f"fe_Repatriation_{idx+1}_{pair_idx}"]
            g.add((repatriation_event_uri, RDF.type, F.Repatriation))
            g.add((repatriation_event_uri, RDF.type, F.IndividualEvent))
            g.add((person_uri, PROP_composedOf, repatriation_event_uri))
            g.add((event_uri, TEMP.before, repatriation_event_uri))
            g.add((repatriation_event_uri, PROP_temporal_after, event_uri))
            if birth_country:
                g.add((repatriation_event_uri, PROP_targetCountry, birth_country))
            if collective_event_uri is not None:
                g.add((repatriation_event_uri, F.group, collective_event_uri))
            count_repatriation += 1

    # INHUMATION
    comm_enterrement = row.get("Comm_enterrement", "")
    if comm_enterrement and not is_missing(comm_enterrement):
        lat_ent = row.get("Coord_Lat_enterrement", "") or row.get("Coord_lat_enterrement", "")
        lon_ent = row.get("Coord_Long_enterrement", "") or row.get("Coord_long_enterrement", "")

        lat_e = None
        lon_e = None
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

        is_inhumation_geocoded = False
        if (lat_e is None or lon_e is None):
            # Essayer d'abord le cimetière (burial/cemetery)
            comm_key = str(comm_enterrement).strip()
            if comm_key in geocode_cache_cemetery and geocode_cache_cemetery[comm_key][0] is not None:
                lat_e, lon_e = geocode_cache_cemetery[comm_key]
                is_inhumation_geocoded = True
            else:
                # Sinon, fallback sur le cache de commune régulier
                cached = geocode_cache_inhumation.get(comm_key, (None, None))
                if cached[0] is not None:
                    lat_e, lon_e = cached
                    is_inhumation_geocoded = True

        for pair_idx, (person_uri, event_uri) in enumerate(person_event_pairs, start=1):
            inhumation_event_uri = DATA[f"InhumationEvent_{idx+1}_{pair_idx}"]
            if (inhumation_event_uri, None, None) not in g:
                g.add((inhumation_event_uri, RDF.type, F.Inhumation))
                g.add((inhumation_event_uri, RDF.type, F.IndividualEvent))

            g.add((person_uri, PROP_composedOf, inhumation_event_uri))
            g.add((event_uri, TEMP.before, inhumation_event_uri))
            g.add((inhumation_event_uri, PROP_temporal_after, event_uri))
            if collective_event_uri is not None:
                g.add((inhumation_event_uri, F.group, collective_event_uri))

            if lat_e is not None and lon_e is not None:
                is_suspicious, reason = is_suspicious_coordinate(lat_e, lon_e)
                if not is_suspicious:
                    geometry_inhumation_uri = DATA[f"fe_geometry_inhumation_{idx+1}_{pair_idx}"]
                    if add_or_update_geometry(
                        g,
                        inhumation_event_uri,
                        geometry_inhumation_uri,
                        location_label=comm_enterrement,
                        lat=lat_e,
                        lon=lon_e,
                        is_geocoded=is_inhumation_geocoded,
                    ):
                        count_geometry_nodes += 1
                        count_geometry_with_wkt += 1
                        if is_inhumation_geocoded and comm_enterrement and not is_missing(comm_enterrement):
                            g.add((inhumation_event_uri, F.lieu, Literal(str(comm_enterrement).strip())))
                else:
                    print(f"  ⚠️  Coordonnée suspecte ignorée pour inhumation ({reason}): {lon_e}, {lat_e}")

            count_inhumation += 1

    # SOURCE
    source_name = row.get("source", "") or row.get("Source", "")
    url2 = row.get("url2", "") or row.get("URL2", "")

    if not is_missing(source_name) or not is_missing(url2):
        source_uri = DATA[f"fe_Source_{idx+1}"]
        g.add((source_uri, RDF.type, SOURCE_CLASS))
        combined_fe_source = " ".join(filter(None, [str(source_name).strip() if not is_missing(source_name) else "", str(url2).strip() if not is_missing(url2) else ""]))
        source_category = infer_source_category_key(combined_fe_source)
        SOURCE_SUBTYPE_MAP = {
            "family": F.Family, 
            "media": F.Media, 
            "civil_society": F.CivilSociety, 
            "death_certificate": F.DeathCertificate, 
            "official_document": F.OfficialDocument,
            "other_official_document": F.OtherOfficialDocument
        }
        sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
        if sub_type:
            g.add((source_uri, RDF.type, sub_type))
        else:
            # Default to Media if category unknown
            g.add((source_uri, RDF.type, F.Media))
        if not is_missing(source_name):
            g.add((source_uri, RDFS.label, Literal(str(source_name).strip())))
        if not is_missing(url2):
            g.add((source_uri, PROP_hasWebLink, Literal(str(url2).strip())))

        for _, event_uri in all_event_pairs:
            g.add((event_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

    additional_counts = add_additional_typed_events(
        g,
        person_event_pairs,
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "fe",
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
count_geom_propagated = propagate_geometry_to_sibling_events(g, F, GEO, RDF, Literal, "fortress_europe")
count_event_country_from_geometry = add_event_country_from_geometry(g, F, DATA, GEO, RDF, RDFS, Literal, "fortress_europe")

# Integrite metier: une personne doit avoir un resultat final (Death ou Missing).
invalid_injury_only_persons = []
for person_uri in g.subjects(RDF.type, PERSON_CLASS):
    has_injury = False
    has_terminal_event = False
    for event_uri in g.objects(person_uri, PROP_composedOf):
        if (event_uri, RDF.type, INJURY_EVENT_CLASS) in g:
            has_injury = True
        if (event_uri, RDF.type, DEATH_EVENT_CLASS) in g or (event_uri, RDF.type, MISSING_EVENT_CLASS) in g:
            has_terminal_event = True
    if has_injury and not has_terminal_event:
        invalid_injury_only_persons.append(person_uri)

if invalid_injury_only_persons:
    sample = ", ".join(str(u) for u in invalid_injury_only_persons[:5])
    raise RuntimeError(
        "Integrity error: Injury-only persons detected (must have Death or Missing). "
        f"count={len(invalid_injury_only_persons)} sample={sample}"
    )

g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "="*60)
print("Import Fortress Europe complete.")
print("="*60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created: {count_death_events}")
print(f"Injury events created: {count_injury_events}")
print(f"Missing events created: {count_missing_events}")
print(f"Rows with >=2 people involved (from text): {count_rows_multi_people}")
print(f"Transport individuals created: {count_transports}")
print(f"Embark events created: {count_embark}")
print(f"Collective events created: {count_collective_events}")
print(f"Repatriation events created: {count_repatriation}")
geometry_nodes_created = len(set(g.subjects(RDF.type, GEO.Geometry)))
geometry_nodes_with_wkt = len(set(g.subjects(GEO.asWKT, None)))

print(f"Inhumation events created: {count_inhumation}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Geometry nodes created: {geometry_nodes_created}")
print(f"Geometry nodes with WKT: {geometry_nodes_with_wkt}")
print(f"Sources created: {count_sources}")
print(f"Death certificates created: {count_death_certificates}")
print(f"\nCause de décès - mapping avec thésaurus:")
print(f"  - Matched to thesaurus URI: {count_cause_matched}")
print(f"  - Added as literal (fallback): {count_cause_literal}")
print(f"\nDétection d'accidents de circulation:")
print(f"  - Accidents détectés (percuté/renversé/accident): {count_traffic_accidents}")
print(f"  - Moyen de transport identifié: {count_transport_identified}")
print(f"Geometry propagated to siblings: {count_geom_propagated}")
print(f"Event countries from geometry: {count_event_country_from_geometry}")
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

