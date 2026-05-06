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
import random
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
CSV_PATH = "fortress_europe/fortress_europe.csv"
OUTPUT_TTL = "fortress_europe/frontlet_import_output.ttl"
MAPPING_PATH = "fortress_europe/mappingFeThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)
GEOCODE_SAMPLE_SIZE = 30  # Géocoder seulement N lignes aléatoires pour accélérer.
GEOCODE_RANDOM_SEED = 42
GEOCODE_CACHE_PATH = "fortress_europe/geocode_cache.json"
GEOCODE_USE_CEMETERY_SEARCH = False  # Réduit fortement les appels API et les 429.
GEOCODE_MIN_DELAY_SECONDS = 1.2  # Délai minimal entre 2 requêtes HTTP Nominatim.
GEOCODE_429_BACKOFF_SECONDS = 8.0  # Pause après un 429 avant un nouvel essai.
GEOCODE_MAX_429_RETRIES = 3  # Nombre d'essais supplémentaires après 429.
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
geolocator = Nominatim(user_agent="frontlet_fe_geocoder")
GEOCODER_RATE_LIMITED = False
LAST_GEOCODE_REQUEST_TS = 0.0


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
            result = geolocator.geocode(query_text, timeout=timeout)
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
    Cherche d'abord un cimetière, sinon utilise le centroïde de la ville.
    """
    if is_missing(location_name):
        return None, None

    global GEOCODER_RATE_LIMITED
    if GEOCODER_RATE_LIMITED:
        return None, None
    
    location_str = str(location_name).strip()
    
    # Optionnel: chercher un cimetière avant le géocodage standard.
    for attempt in range(max_retries):
        try:
            if GEOCODE_USE_CEMETERY_SEARCH:
                # Version allégée: si activé, on tente seulement un point "cemetery <lieu>".
                cemetery_query = f"cemetery {location_str}"
                cemetery_location = geocode_single_query(cemetery_query, timeout=10)
                if cemetery_location:
                    return cemetery_location.latitude, cemetery_location.longitude
            
            # Si pas de cimetière unique, chercher le centroïde de la ville
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
    }

    tokens = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ'’.-]+", txt)
    if not tokens or len(tokens) > 6:
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


def extract_location_from_text(text_value):
    """Try to detect a location mention from narrative text."""
    if is_missing(text_value):
        return None

    text = str(text_value).strip()
    if not text:
        return None

    patterns = [
        r"\b(?:rotta per|route to|heading to|towards?|diretti a|diretto a|en route to)\s+(?P<loc>[^,.;:()]{2,100})",
        r"\b(?:al largo di|au large de|off the coast of)\s+(?P<loc>[^,.;:()]{2,100})",
        r"\b(?:near|close to|vicino a|nei pressi di|in prossimita di|in prossimità di)\s+(?P<loc>[^,.;:()]{2,100})",
        r"\b(?:in|at)\s+(?P<loc>[A-Z][^,.;:()]{2,100})",
        r"\ba\s+(?P<loc>[A-Z][A-Za-zÀ-ÖØ-öø-ÿ'’.-]{1,40}(?:\s+(?:[A-Z][A-Za-zÀ-ÖØ-öø-ÿ'’.-]{1,40}|di|de|del|della|delle|da|al|alla)){0,4})",
    ]

    for pattern in patterns:
        match = re.search(pattern, text, flags=re.IGNORECASE)
        if match:
            cleaned = clean_extracted_location(match.group("loc"))
            if cleaned and is_plausible_place_name(cleaned):
                return cleaned

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
    """Load geocoding cache from disk: {location: [lat, lon]}."""
    if not os.path.exists(cache_path):
        return {}
    try:
        with open(cache_path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        cache = {}
        for key, value in data.items():
            if isinstance(value, list) and len(value) == 2:
                lat, lon = value
                if lat is not None and lon is not None:
                    cache[str(key)] = (float(lat), float(lon))
        print(f"Cache géocodage chargé: {len(cache)} lieux")
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


def add_or_update_geometry(g, event_uri, geometry_uri, location_label=None, lat=None, lon=None):
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

    wkt = f"POINT({lon_f} {lat_f})"
    g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
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

# Échantillon aléatoire des lignes sur lesquelles on autorise le géocodage.
sample_size = min(GEOCODE_SAMPLE_SIZE, n_rows)
rng = random.Random(GEOCODE_RANDOM_SEED)
geocode_row_indices = set(rng.sample(list(df.index), sample_size)) if sample_size > 0 else set()
print(f"Géocodage activé sur {sample_size}/{n_rows} lignes (échantillon aléatoire, seed={GEOCODE_RANDOM_SEED})")
print(
    "Paramètres anti-429: "
    f"min_delay={GEOCODE_MIN_DELAY_SECONDS}s, "
    f"backoff={GEOCODE_429_BACKOFF_SECONDS}s, "
    f"max_429_retries={GEOCODE_MAX_429_RETRIES}"
)

# ------------------- Cache de geocodage ------------------
def build_geocode_cache(values, label="lieux", persistent_cache=None):
    """Geocode each distinct non-empty value once and return {value: (lat, lon)}."""
    cache = {}
    if persistent_cache is None:
        persistent_cache = {}
    unique_values = sorted({str(v).strip() for v in values if not is_missing(v) and str(v).strip()})
    total = len(unique_values)

    if total == 0:
        return cache

    hits = sum(1 for value in unique_values if value in persistent_cache)
    print(f"Pré-géocodage: {total} {label} uniques (cache hit={hits}, online={total-hits})")
    for i, value in enumerate(unique_values, start=1):
        if value in persistent_cache:
            cache[value] = persistent_cache[value]
            continue
        if GEOCODER_RATE_LIMITED:
            print(f"  Pré-géocodage {label}: interrompu à {i-1}/{total} (rate limit)")
            break
        coords = geocode_location(value)
        cache[value] = coords
        if coords[0] is not None and coords[1] is not None:
            persistent_cache[value] = coords
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


# Préparer les listes de valeurs à géocoder uniquement quand c'est nécessaire.
persistent_geocode_cache = load_persistent_geocode_cache()
rows_needing_lieu_geocode = []
rows_needing_inhumation_geocode = []
row_location_choice = {}

count_location_from_text = 0
count_location_from_lieu = 0
count_location_missing = 0
count_sample_rows_missing_coords = 0
count_sample_rows_with_coords = 0
count_sample_rows_with_geocodable_location = 0

for prep_idx, prep_row in df.iterrows():
    lat_deces = prep_row.get("Coord_Lat_deces", "") or prep_row.get("Coord_lat_deces", "")
    lon_deces = prep_row.get("Coord_Long_deces", "") or prep_row.get("Coord_long_deces", "")
    text_prep = prep_row.get("text", "")
    lieu_prep = prep_row.get("lieu", "") or prep_row.get("lieu".lower(), "")

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

    if prep_idx in geocode_row_indices:
        if is_missing(lat_deces) or is_missing(lon_deces):
            count_sample_rows_missing_coords += 1
            if is_geocodable_location_text(location_choice):
                rows_needing_lieu_geocode.append(location_choice)
                count_sample_rows_with_geocodable_location += 1
        else:
            count_sample_rows_with_coords += 1

    lat_ent_prep = prep_row.get("Coord_Lat_enterrement", "") or prep_row.get("Coord_lat_enterrement", "")
    lon_ent_prep = prep_row.get("Coord_Long_enterrement", "") or prep_row.get("Coord_long_enterrement", "")
    comm_enterrement_prep = prep_row.get("Comm_enterrement", "")
    if prep_idx in geocode_row_indices and (is_missing(lat_ent_prep) or is_missing(lon_ent_prep)):
        if is_geocodable_location_text(comm_enterrement_prep):
            rows_needing_inhumation_geocode.append(str(comm_enterrement_prep).strip())

geocode_cache_lieu = build_geocode_cache(rows_needing_lieu_geocode, label="lieux de décès", persistent_cache=persistent_geocode_cache)
geocode_cache_inhumation = build_geocode_cache(rows_needing_inhumation_geocode, label="lieux d'inhumation", persistent_cache=persistent_geocode_cache)
save_persistent_geocode_cache(persistent_geocode_cache)
print(
    "Détection de lieu (toutes lignes): "
    f"depuis text={count_location_from_text}, "
    f"fallback lieu={count_location_from_lieu}, "
    f"sans lieu={count_location_missing}"
)
print(
    "Diagnostic échantillon géocodage: "
    f"lignes avec coords déjà présentes={count_sample_rows_with_coords}, "
    f"lignes sans coords={count_sample_rows_missing_coords}, "
    f"lignes géocodables (sans coords)={count_sample_rows_with_geocodable_location}"
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
    if injury_count > 0 and (dead_count + missing_count) == 0:
        # Injury est ante-mortem et doit etre ancre a un evenement de deces ou de disparition.
        missing_count = 1
    people_involved_for_row = dead_count + injury_count + missing_count

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
    for i in range(injury_count):
        event_specs.append((INJURY_EVENT_CLASS, "Injury", i + 1))
    for i in range(missing_count):
        event_specs.append((MISSING_EVENT_CLASS, "Missing", i + 1))

    person_event_pairs = []
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
        elif event_kind == "Injury":
            count_injury_events += 1
        elif event_kind == "Missing":
            count_missing_events += 1
            primary_event_uris.append(event_uri)

        person_event_pairs.append((person_uri, event_uri))

    if primary_event_uris:
        for _, event_uri in person_event_pairs:
            if (event_uri, RDF.type, INJURY_EVENT_CLASS) in g:
                anchor_event_uri = primary_event_uris[0]
                g.add((event_uri, PROP_temporal_before, anchor_event_uri))
                g.add((anchor_event_uri, PROP_temporal_after, event_uri))

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
    except Exception:
        pass

    # SEXE (inference textuelle depuis les récits)
    sexe = norm(row.get("text", "") or row.get("NOTA", "") or row.get("Description", ""))
    if sexe and not is_missing(sexe):
        for person_uri, _ in person_event_pairs:
            if any(k in sexe for k in (" hombre ", "hombre", " varon", "varón", " male ", " man ", " boy ", " nino", "niño")):
                if THES_male is not None:
                    g.add((person_uri, F.gender, THES_male))
                else:
                    g.add((person_uri, F.gender, Literal("male")))
            elif any(k in sexe for k in (" mujer ", "mujer", " female ", " woman ", " girl ", " nina", "niña")):
                if THES_female is not None:
                    g.add((person_uri, F.gender, THES_female))
                else:
                    g.add((person_uri, F.gender, Literal("female")))

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
                for _, event_uri in person_event_pairs:
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
            for _, event_uri in person_event_pairs:
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
            for _, event_uri in person_event_pairs:
                g.add((event_uri, PROP_borderOUT, cnode))

    # frontiere_IN -> borderIN
    front_in = row.get("Frontiere_IN", "") or row.get("frontiere_IN", "") or row.get("frontiere_IN".lower(), "")
    if not is_missing(front_in):
        cnode = ensure_country_node(g, str(front_in).strip())
        if cnode:
            for _, event_uri in person_event_pairs:
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

    if lat_f is None or lon_f is None:
        if idx in geocode_row_indices and not is_missing(lieu_val):
            try:
                lat_lieu, lon_lieu = geocode_cache_lieu.get(str(lieu_val).strip(), (None, None))
                if lat_lieu is not None and lon_lieu is not None and math.isfinite(lat_lieu) and math.isfinite(lon_lieu):
                    is_suspicious, reason = is_suspicious_coordinate(lat_lieu, lon_lieu)
                    if is_suspicious:
                        print(f"  ⚠️  Coordonnée suspecte ignorée pour lieu ({reason}): {lon_lieu}, {lat_lieu}")
                    else:
                        lat_f = lat_lieu
                        lon_f = lon_lieu
            except Exception as e:
                print(f"Erreur géocodage lieu pour ligne {idx+1}: {lieu_val} - {e}")

    for pair_idx, (_, event_uri) in enumerate(person_event_pairs, start=1):
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
                    embark_uri = DATA[f"EmbarkEvent_{idx+1}_{slug}_{pair_idx}"]
                    if (embark_uri, None, None) not in g:
                        g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                    g.add((embark_uri, PROP_usedIn, transport_uri))
                    g.add((embark_uri, PROP_temporal_before, event_uri))
                    g.add((event_uri, PROP_temporal_after, embark_uri))
                    g.add((person_uri, PROP_composedOf, embark_uri))
                    if collective_event_uri is not None:
                        g.add((embark_uri, F.group, collective_event_uri))
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

        if (lat_e is None or lon_e is None) and idx in geocode_row_indices:
            lat_e, lon_e = geocode_cache_inhumation.get(str(comm_enterrement).strip(), (None, None))

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
                    ):
                        count_geometry_nodes += 1
                        count_geometry_with_wkt += 1
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
        SOURCE_SUBTYPE_MAP = {"family": F.Family, "media": F.Media, "civil_society": F.CivilSociety, "death_certificate": F.DeathCertificate, "official_document": F.OtherOfficialDocument}
        sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
        if sub_type:
            g.add((source_uri, RDF.type, sub_type))
        if not is_missing(source_name):
            g.add((source_uri, RDFS.label, Literal(str(source_name).strip())))
        if not is_missing(url2):
            g.add((source_uri, PROP_hasWebLink, Literal(str(url2).strip())))

        for _, event_uri in person_event_pairs:
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
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

