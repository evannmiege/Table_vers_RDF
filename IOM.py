#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer CSV Sud UE → ontologie RDF selon vos règles.
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
    add_event_country_from_geometry,
    build_additional_event_specs,
    build_cemetery_geocode_cache,
    build_wkt_for_location_precision,
    collect_text_values_from_row,
    infer_day_of_week_name,
    propagate_geometry_to_sibling_events,
)

# -------------------- CONFIGURATION --------------------
ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
CSV_PATH = "IOM/IOM.csv"
OUTPUT_TTL = "IOM/frontlet_import_output.ttl"
MAPPING_PATH = "IOM/mappingIOMThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)
MAX_ROWS = None  # None pour traiter toutes les lignes
MAX_GEOCODING_CALLS = 20  # Limite le nombre total d'appels de géocodage
_geocoding_call_count = 0
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

# Initialiser le géocodeur
geolocator = Nominatim(user_agent="frontlet_iom_geocoder")

def geocode_location(location_name, max_retries=3):
    """
    Géocode un nom de lieu et retourne (latitude, longitude) ou (None, None).
    Cherche d'abord un cimetière, sinon utilise le centroïde de la ville.
    """
    global _geocoding_call_count
    if is_missing(location_name):
        return None, None
    
    if _geocoding_call_count >= MAX_GEOCODING_CALLS:
        return None, None
    _geocoding_call_count += 1
    
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

def parse_coordinate_value(value):
    """
    Extrait une coordonnée numérique depuis des chaînes comme:
    'LAT 39.214156', 'LONG 26.564986', ou '39.214156'.
    Retourne un float ou None.
    """
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


def parse_coordinate_pair(value):
    """
    Extrait un couple (latitude, longitude) depuis une chaîne comme
    '32.55058, 20.557715'.
    Le premier nombre est la latitude, le second la longitude.
    """
    if is_missing(value):
        return None, None

    text = str(value).strip()
    matches = re.findall(r"[-+]?\d+(?:[\.,]\d+)?", text)
    if len(matches) < 2:
        return None, None

    try:
        lat = float(matches[0].replace(",", "."))
        lon = float(matches[1].replace(",", "."))
        return lat, lon
    except Exception:
        return None, None

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
    
    # Mots-clés d'accident (dataset en anglais)
    accident_keywords = ["hit by", "struck by", "run over", "crash", "collision", "accident"]
    
    # Vérifier si un mot-clé d'accident est présent
    has_accident = any(keyword in text_norm for keyword in accident_keywords)
    
    if not has_accident:
        return False, None
    
    # Liste des moyens de transport à rechercher (dataset en anglais)
    transport_patterns = [
        ("train", ["train", "locomotive", "railway"]),
        ("car", ["car", "auto", "automobile", "vehicle", "van"]),
        ("truck", ["truck", "lorry", "semi-trailer", "semi trailer", "heavy goods vehicle"]),
        ("bus", ["bus", "coach", "minibus"]),
        ("motorbike", ["motorbike", "motorcycle", "scooter"]),
        ("bicycle", ["bicycle", "bike", "cyclist", "pushbike"]),
        ("tram", ["tram", "tramway", "streetcar"]),
        ("boat", ["boat", "ship", "vessel", "ferry", "patera", "cayuco"]),
        ("plane", ["plane", "airplane", "aircraft"]),
    ]
    
    # Chercher quel transport est mentionné
    for transport_name, keywords in transport_patterns:
        for keyword in keywords:
            if keyword in text_norm:
                return True, transport_name
    
    # Accident détecté mais transport non identifié
    return True, None


def detect_transport_from_text(text):
    """Detect a transport category from free text and return a canonical token."""
    if is_missing(text):
        return None

    text_norm = norm(text)
    transport_patterns = [
        ("boat", ["boat", "ship", "vessel", "ferry", "patera", "cayuco", "barco", "barcone"]),
        ("train", ["train", "locomotive", "railway"]),
        ("truck", ["truck", "lorry", "semi-trailer", "semi trailer", "heavy goods vehicle"]),
        ("bus", ["bus", "coach", "minibus"]),
        ("car", ["car", "auto", "automobile", "vehicle", "van"]),
        ("motorbike", ["motorbike", "motorcycle", "scooter"]),
        ("bicycle", ["bicycle", "bike", "cyclist", "pushbike"]),
        ("tram", ["tram", "tramway", "streetcar"]),
        ("plane", ["plane", "airplane", "aircraft"]),
    ]

    for transport_name, keywords in transport_patterns:
        if any(keyword in text_norm for keyword in keywords):
            return transport_name

    return None

def ensure_country_node(g, country_code_or_name):
    """
    Try to find a country resource in graph by label or prefLabel or ISO code.
    Returns the country URIRef or None.
    """
    if is_missing(country_code_or_name):
        return None

    val = clean_country_token(country_code_or_name)
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
        uri = DATA["iom_Country_" + iso3.upper()]
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
    uri = DATA["iom_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(country_code_or_name)))
    return uri

COUNTRY_ALIASES = {
    "turkiye": "Turkey",
    "türkiye": "Turkey",
    "tuerkiye": "Turkey",
    "t?rkiye": "Turkey",
    "western sahara": "Western Sahara",
    "uk": "United Kingdom",
}

COUNTRY_TEXT_LOOKUP = {}
for _country in pycountry.countries:
    for _label in {
        getattr(_country, "name", None),
        getattr(_country, "official_name", None),
        getattr(_country, "common_name", None),
    }:
        if _label:
            COUNTRY_TEXT_LOOKUP[norm(_label)] = _country.name
for _alias, _canonical in COUNTRY_ALIASES.items():
    COUNTRY_TEXT_LOOKUP[norm(_alias)] = _canonical

COUNTRY_LOOKUP_ITEMS = sorted(
    COUNTRY_TEXT_LOOKUP.items(),
    key=lambda item: len(item[0]),
    reverse=True,
)


def clean_country_token(value):
    """Strip stray surrounding quotes/punctuation from a country token."""
    if value is None:
        return ""
    return str(value).strip().strip("'\"`‘’“” ")


def resolve_country_name(value):
    """Resolve a raw value to a canonical country name if possible."""
    if is_missing(value):
        return None

    candidate = clean_country_token(value).strip(" .,-;:/")
    if not candidate:
        return None

    direct_match = COUNTRY_TEXT_LOOKUP.get(norm(candidate))
    if direct_match:
        return direct_match

    try:
        matches = pycountry.countries.search_fuzzy(candidate)
        if matches:
            return matches[0].name
    except Exception:
        pass

    return None


def ensure_country_nodes(g, raw_value):
    """Return one or more country nodes from a possibly multi-valued field."""
    if is_missing(raw_value):
        return []

    raw_text = clean_country_token(raw_value)
    if not raw_text:
        return []

    # First try to resolve the full value as a single country name.
    resolved_single = resolve_country_name(raw_text)
    if resolved_single is not None:
        values = [resolved_single]
    else:
        values = re.split(r"\s*[,;/]\s*", raw_text)

    nodes = []
    seen = set()
    for value in values:
        cleaned_value = clean_country_token(value)
        if is_missing(cleaned_value):
            continue
        country_node = ensure_country_node(g, cleaned_value)
        if country_node is not None and str(country_node) not in seen:
            nodes.append(country_node)
            seen.add(str(country_node))
    return nodes

def find_country_mentions_in_text(text):
    """Return ordered unique country names mentioned in a free-text string."""
    if is_missing(text):
        return []

    text_norm = norm(text)
    matches = []
    for label_norm, canonical_name in COUNTRY_LOOKUP_ITEMS:
        for match in re.finditer(rf"(?<!\w){re.escape(label_norm)}(?!\w)", text_norm):
            matches.append((match.start(), -len(label_norm), canonical_name))

    matches.sort()
    ordered = []
    seen = set()
    for _, _, canonical_name in matches:
        if canonical_name not in seen:
            ordered.append(canonical_name)
            seen.add(canonical_name)
    return ordered


def pick_last_country_in_segment(text):
    """Return the last country mentioned in a text segment, or None."""
    mentions = find_country_mentions_in_text(text)
    return mentions[-1] if mentions else None


def extract_country_from_location(location_text):
    """
    Extract a single death country from a free-text location.

    Rules:
    - return one country only when the death country is identifiable;
    - if the location is genuinely ambiguous (border / between two countries),
      return `Unknown`;
    - when route metadata is present, prefer the country from the death-location
      clause, and only fall back to the final destination clause if needed.
    """
    if is_missing(location_text):
        return ["Unknown"]

    text = str(location_text).strip()
    if not text:
        return ["Unknown"]

    text_norm = norm(text)
    all_mentions = find_country_mentions_in_text(text)
    if not all_mentions:
        return ["Unknown"]

    # Ex.: "in Belarus close to the border with Latvia" -> garder Belarus, pas Latvia.
    border_with_match = re.search(r"\bborder with\b", text_norm)
    if border_with_match:
        before_border = text[:border_with_match.start()]
        country_before_border = pick_last_country_in_segment(before_border)
        if country_before_border:
            return [country_before_border]
        return ["Unknown"]

    # Cas explicitement ambigus : frontière ou zone entre deux pays sans pays de décès clair.
    if len(all_mentions) >= 2:
        if re.search(r"\bborder between\b", text_norm):
            return ["Unknown"]
        if "border gate" not in text_norm and re.search(r"\b(?:on|at)\s+the\s+[^.,;]*\bborder\b", text_norm):
            return ["Unknown"]
        if any(marker in text_norm for marker in ["unspecified location", "unknown location", "undisclosed location"]):
            if "border" in text_norm or re.search(r"\bbetween\b.+\band\b", text_norm):
                return ["Unknown"]

    # Partie principale du lieu de décès : on retire les informations de trajet/départ.
    location_scope = re.split(
        r"\s+-\s+|;|\b(?:en route to|on the way to|heading to|towards?|departure from|departed from|embarkation from|embarked from|presumed departure from)\b",
        text,
        maxsplit=1,
        flags=re.IGNORECASE,
    )[0].strip()

    location_country = pick_last_country_in_segment(location_scope)
    if location_country:
        return [location_country]

    # Si le lieu principal est non spécifié, regarder une éventuelle destination finale explicite.
    destination_match = re.search(
        r"\b(?:en route to|on the way to|heading to|towards?)\b(?P<dest>.+)$",
        text,
        flags=re.IGNORECASE,
    )
    if destination_match:
        destination_country = pick_last_country_in_segment(destination_match.group("dest"))
        if destination_country:
            return [destination_country]

    return ["Unknown"]

def create_age_node(g, age_value, row_index=None):
    """Create an Age instance and return it."""
    if age_value is None or is_missing(age_value):
        return None
    try:
        age_num = int(float(str(age_value).strip()))
    except Exception:
        return None
    if row_index is None:
        age_uri = BNode()
    else:
        age_uri = DATA[f"iom_Age_{row_index + 1}"]
    g.add((age_uri, RDF.type, F.Age))
    g.add((age_uri, F.hasAge, Literal(age_num, datatype=XSD.integer)))
    g.add((age_uri, PROP_hasPrecision, Literal(True, datatype=XSD.boolean)))
    return age_uri


def parse_age_from_text(*values):
    """Extract one precise age from free text (e.g. 12 years old, 25-year-old)."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return None

    patterns = [
        r"\b(\d{1,3})\s*(?:years?\s*old|yrs?\s*old|year-old|yo)\b",
        r"\baged\s*(\d{1,3})\b",
    ]
    for pattern in patterns:
        match = re.search(pattern, txt)
        if not match:
            continue
        try:
            age_val = int(match.group(1))
            if 0 < age_val <= 120:
                return age_val
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
        match = re.search(pattern, txt)
        if not match:
            continue
        try:
            age_min = int(match.group(1))
            age_max = int(match.group(2))
            if 0 < age_min <= 120 and 0 < age_max <= 120:
                return (min(age_min, age_max), max(age_min, age_max))
        except Exception:
            continue
    return None


def create_age_interval_node(g, age_interval, row_index=None):
    """Create an AgeInterval instance and return it."""
    if not age_interval:
        return None
    age_min, age_max = age_interval
    if row_index is None:
        interval_uri = BNode()
    else:
        interval_uri = DATA[f"iom_AgeInterval_{row_index + 1}"]
    g.add((interval_uri, RDF.type, F.AgeInterval))
    g.add((interval_uri, RDFS.label, Literal(f"{age_min}-{age_max} years")))
    return interval_uri

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


def find_typed_thesaurus_term_by_labels(g, class_uri, labels):
    """Find a thesaurus individual of type class_uri by one of the provided labels."""
    if class_uri is None:
        return None
    for label in labels:
        if label is None or str(label).strip() == "":
            continue
        lbl_norm = norm(label)
        for s in g.subjects(RDF.type, class_uri):
            for p in (SKOS.prefLabel, RDFS.label):
                for o in g.objects(s, p):
                    if norm(o) == lbl_norm:
                        return s
    return None


def copy_all_class_hierarchy(g_src, g_dst):
    """Copy all ontology class declarations and subclass links into the output graph."""
    class_predicates = (RDF.type, RDFS.subClassOf, SKOS.prefLabel, SKOS.definition, RDFS.label)
    frontlet_ns = str(F)
    class_uris = {
        subject
        for subject in g_src.subjects(RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class"))
        if str(subject).startswith(frontlet_ns)
    }
    expanded_class_uris = set(class_uris)
    for class_uri in list(class_uris):
        for subj, _, _ in g_src.triples((None, RDFS.subClassOf, class_uri)):
            if str(subj).startswith(frontlet_ns):
                expanded_class_uris.add(subj)

    for class_uri in expanded_class_uris:
        for predicate in class_predicates:
            for _, _, obj in g_src.triples((class_uri, predicate, None)):
                g_dst.add((class_uri, predicate, obj))

def get_source_type_class(info_source):
    """Map Information Source to one of: OfficialDocument, Family, Media, CivilSociety."""
    if is_missing(info_source):
        return SOURCE_MEDIA_CLASS

    source_norm = norm(info_source)
    tokens = set(re.findall(r"[a-z0-9]+", source_norm))

    def has_word(*words):
        return any(word in tokens for word in words)

    def has_phrase(*phrases):
        return any(phrase in source_norm for phrase in phrases)

    # 0) Sources de certificats de deces
    if has_phrase("death certificate", "certificate of death", "certificat de deces"):
        return SOURCE_DEATH_CERTIFICATE_CLASS

    # 1) Official / institutional sources
    if (
        has_word(
            "official", "government", "minister", "ministry", "embassy", "consulate",
            "parliament", "prefecture", "governor", "governorate", "municipality",
            "police", "coastguard", "officiel", "gouvernement", "ministere"
        )
        or has_phrase("coast guard", "state border guard", "ministry of", "government of")
    ):
        return SOURCE_OTHER_OFFICIAL_DOC_CLASS

    # 2) Civil society / NGOs / activist collectives
    if (
        has_word("ngo", "ngos", "association", "charity", "civil", "amnesty", "rights")
        or has_phrase(
            "civil society", "société civile", "societe civile", "alarm phone",
            "caminando fronteras", "amdh", "human rights", "sea watch", "sea-eye"
        )
    ):
        return SOURCE_CIVIL_SOCIETY_CLASS

    # 3) Family or close relatives only — require explicit phrases, never single ambiguous words
    if has_phrase(
        "family member", "family members", "next of kin", "membre de la famille",
        "famille de la victime", "relatives of", "parents of", "testified by family",
        "survivor's family", "victim's family"
    ):
        return SOURCE_FAMILY_CLASS

    # 4) Media (explicite ou par defaut)
    if (
        has_word("media", "news", "press", "journalist", "newspaper", "radio", "tv", "blog", "journal", "presse")
        or has_phrase("news agency", "via facebook", "via twitter")
    ):
        return SOURCE_MEDIA_CLASS

    return SOURCE_MEDIA_CLASS

def create_or_get_death_cause_instance(g, cause_text):
    """Create or retrieve a DeathCause instance from the cause text."""
    if is_missing(cause_text):
        return None
    
    cause_slug = re.sub(r'[^a-z0-9_]', '_', norm(cause_text).strip())
    if not cause_slug or cause_slug in ("nan", "none", ""):
        return None
    
    cause_uri = DATA["iom_DeathCause_" + cause_slug]
    
    # Ajouter seulement si non deja cree
    if (cause_uri, RDF.type, DEATH_CAUSE_CLASS) not in g:
        g.add((cause_uri, RDF.type, DEATH_CAUSE_CLASS))
        g.add((cause_uri, RDFS.label, Literal(str(cause_text).strip())))
    
    return cause_uri


def create_or_get_death_nature_instance(g, nature_text):
    """Create or retrieve a DeathNature instance from a nature label."""
    if is_missing(nature_text):
        return None

    nature_slug = re.sub(r"[^a-z0-9_]", "_", norm(nature_text).strip())
    if not nature_slug or nature_slug in ("nan", "none", ""):
        return None

    nature_uri = DATA["iom_DeathNature_" + nature_slug]
    if (nature_uri, RDF.type, F.DeathNature) not in g:
        g.add((nature_uri, RDF.type, F.DeathNature))
        g.add((nature_uri, RDFS.label, Literal(str(nature_text).strip())))
    return nature_uri


def ensure_gender_instances(graph):
    """Create canonical frontlet:Gender individuals for IOM export."""
    entries = {
        "male": (DATA["iom_Gender_male"], "male", THES_male),
        "female": (DATA["iom_Gender_female"], "female", THES_female),
    }
    for _, (uri, label, match_uri) in entries.items():
        graph.add((uri, RDF.type, F.Gender))
        graph.add((uri, RDFS.label, Literal(label, lang="en")))
        if match_uri is not None:
            graph.add((uri, SKOS.closeMatch, match_uri))
    return {k: v[0] for k, v in entries.items()}


def estimate_injury_count_from_text(*values):
    """Estimate injured victims count from text fields."""
    text = " ".join(str(v) for v in values if v is not None)
    txt = norm(text)
    if txt == "":
        return 0

    number_match = re.search(r"\b(\d{1,3})\s+(?:injured|wounded|hurt)\b", txt)
    if number_match:
        try:
            return max(0, int(number_match.group(1)))
        except Exception:
            pass

    if any(k in txt for k in ["injured", "wounded", "hurt", "bless"]):
        return 1
    return 0

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
    Load optional CSV mapping: col1=IOM_value, col2=Thesaurus_prefLabel, col3=Nature (optional)
    Returns (mapping_dict, mapping_nature):
      - mapping_dict:   normalized_iom_value -> normalized_thesaurus_label
      - mapping_nature: normalized_iom_value -> nature_label_string
    """
    mapping = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, will use direct matching only")
        return mapping, mapping_nature
    try:
        mdf = None
        for _enc in ["utf-8", "utf-8-sig", "cp1252", "latin-1"]:
            try:
                mdf = pd.read_csv(mapping_path, sep=";", dtype=str, encoding=_enc)
                break
            except UnicodeDecodeError:
                continue
        if mdf is None:
            print(f"Warning: Could not decode {mapping_path} with any known encoding")
            return mapping, mapping_nature
        cols = list(mdf.columns)
        if len(cols) >= 2:
            iom_col = cols[0]
            thes_col = cols[1]
            nature_col = cols[2] if len(cols) >= 3 and "nature" in cols[2].lower() else None
            for _, r in mdf.iterrows():
                a = norm(r.get(iom_col, ""))
                t = norm(r.get(thes_col, ""))
                if a and t:
                    mapping[a] = t
                if nature_col:
                    n = str(r.get(nature_col, "")).strip()
                    if a and n and n.lower() not in ("nan", "none", ""):
                        mapping_nature[a] = n
            print(f"Loaded {len(mapping)} IOM->Thesaurus mappings and {len(mapping_nature)} Nature mappings from CSV")
            print(f"Columns used: '{iom_col}' -> '{thes_col}'" + (f" + '{nature_col}'" if nature_col else ""))
        else:
            print(f"Warning: Expected at least 2 columns in {mapping_path}")
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping, mapping_nature

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

# Charger le thesaurus DeathCause et le mapping
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

# Le fichier IOM contient un préambule sur 4 lignes avant la vraie ligne d'en-tête.
# Si les colonnes attendues ne sont pas présentes, on recharge en sautant ce préambule.
if "Incident ID" not in df.columns and "Number Dead" not in df.columns:
    reparsed_df = None
    for _enc in encodings_to_try:
        try:
            reparsed_df = pd.read_csv(
                CSV_PATH,
                sep=";",
                engine="python",
                dtype=str,
                keep_default_na=False,
                na_values=["", "NaN", "nan"],
                encoding=_enc,
                skiprows=4,
            )
            break
        except UnicodeDecodeError:
            continue
    if reparsed_df is not None:
        df = reparsed_df

if MAX_ROWS is not None and len(df) > MAX_ROWS:
    print(f"Info: Limiting processing to first {MAX_ROWS} rows out of {len(df)}")
    df = df.head(MAX_ROWS).copy()

n_rows = len(df)

# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death or F.Event
DEATH_INJURY_EVENT_CLASS = find_by_label(g_ref, "Death injury") or F.DeathInjury
INJURY_EVENT_CLASS = find_by_label(g_ref, "Injury") or F.Injury
MISSING_EVENT_CLASS = F.Missing
CORPSE_REPATRIATION_CLASS = (
    find_by_label(g_ref, "Rapatriement du corps")
    or find_by_label(g_ref, "Corpse repatriation")
    or F.CorpseRepatriation
)
EMBARK_EVENT_CLASS = find_by_label(g_ref, "Embark") or F.EmbarkEvent or F.Event
DEATH_CERTIFICATE_CLASS = find_by_label(g_ref, "DeathCertificate") or F.DeathCertificate

if (MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_EVENT_CLASS, RDFS.subClassOf, F.IndividualEvent))
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
PROP_transportType = find_by_label(g_ref, "transport type") or F.transportType
PROP_transportName = find_by_label(g_ref, "transport name") or F.transportName
PROP_usedIn = find_by_label(g_ref, "Used in") or find_by_label(g_ref, "used in") or F.UsedIn
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_gender = find_by_label(g_ref, "has gender") or F.hasGender
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasWebLink = find_by_label(g_ref, "hasWebLink") or F.hasWebLink
PROP_sourceTitle = find_by_label(g_ref, "article title") or find_by_label(g_ref, "title") or RDFS.label
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_certificate = find_by_label(g_ref, "certificate") or F.certificate
PROP_hasIdCertificate = find_by_label(g_ref, "hasIdCertificate") or F.hasIdCertificate
PROP_hasNarrative = find_by_label(g_ref, "hasNarrative") or F.hasNarrative
PROP_targetCountry = find_by_label(g_ref, "target country") or F.targetCountry
PROP_numberOfSurvivors = find_by_label(g_ref, "number of survivors") or F.numberOfSurvivors
PROP_numberDead = find_by_label(g_ref, "number dead") or F.numberDead
PROP_numberMissing = find_by_label(g_ref, "number of missing") or F.numberMissing
PROP_totalDeadAndMissing = find_by_label(g_ref, "total dead and missing") or F.totalDeadAndMissing
PROP_hasVictimState = find_by_label(g_ref, "has victim state") or F.hasVictimState
PROP_dateDuSite = find_by_label(g_ref, "Date du site") or F.dateDuSite
PROP_dateDeMort = find_by_label(g_ref, "Date de mort") or F.dateDeMort
PROP_hasPrecision = find_by_label(g_ref, "has precision") or F.hasPrecision
PROP_hasAgeInterval = find_by_label(g_ref, "has age interval") or F.hasAgeInterval

THES_male = find_thesaurus_term_by_prefLabel_fr(g_ref, "male") or find_thesaurus_term_by_prefLabel_fr(g_ref, "homme") or T.male
THES_female = find_thesaurus_term_by_prefLabel_fr(g_ref, "female") or find_thesaurus_term_by_prefLabel_fr(g_ref, "femme") or T.female
THES_human = find_thesaurus_term_by_prefLabel_fr(g_ref, "human") or find_thesaurus_term_by_prefLabel_fr(g_ref, "humain") or T.human
THES_VictimState_CLASS = find_by_label(g_ref, "Victim state") or find_by_label(g_ref, "Etat de la victime") or T.VictimState
THES_victim_dead = find_typed_thesaurus_term_by_labels(g_ref, THES_VictimState_CLASS, ["dead", "mort"]) or T.dead
THES_victim_missing = find_typed_thesaurus_term_by_labels(g_ref, THES_VictimState_CLASS, ["missing", "disparu"]) or T.missing
THES_victim_other = find_typed_thesaurus_term_by_labels(g_ref, THES_VictimState_CLASS, ["other", "autre"]) or T.victimState_other
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation", "CorpseRepatriation"])

# Classes de type de source (utiliser directement les URI de l'ontologie)
SOURCE_OFFICIAL_DOC_CLASS = F.OfficialDocument
SOURCE_OTHER_OFFICIAL_DOC_CLASS = F.OtherOfficialDocument
SOURCE_DEATH_CERTIFICATE_CLASS = F.DeathCertificate
SOURCE_FAMILY_CLASS = F.Family
SOURCE_MEDIA_CLASS = F.Media
SOURCE_CIVIL_SOCIETY_CLASS = F.CivilSociety

# DeathCause class
DEATH_CAUSE_CLASS = F.DeathCause

copy_all_class_hierarchy(g_ref, g)
GENDER_URIS = ensure_gender_instances(g)

# ------------------- Traitement des lignes ----------------
created_countries = set()
created_death_events = {}
created_transports = {}
created_collective_events = {}

count_person = 0
count_death_events = 0
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
count_additional_typed_events = 0

for idx, row in df.iterrows():
    embark_uri = None
    repatriation_event_uri = None
    inhumation_event_uri = None

    # EVENEMENTS DE DECES / COLLECTIFS (pilotés par Total Dead and Missing)
    total_dead_missing = parse_int_value(row.get("Total Dead and Missing", "")) or parse_int_value(row.get("Nombre total de morts et de disparus", ""))
    if total_dead_missing is None or total_dead_missing < 1:
        total_dead_missing = 1

    number_dead_count = parse_int_value(row.get("Number Dead", "")) or parse_int_value(row.get("Nombre de morts", "")) or 0
    number_missing_count = parse_int_value(row.get("Minimum Estimated Number of Missing", "")) or parse_int_value(row.get("Nombre minimum estimé de disparus", "")) or 0
    number_dead_count = max(0, number_dead_count)
    number_missing_count = max(0, number_missing_count)

    counted_terminal_events = number_dead_count + number_missing_count
    if counted_terminal_events == 0:
        number_dead_count = total_dead_missing
    elif counted_terminal_events < total_dead_missing:
        if number_dead_count > 0 and number_missing_count == 0:
            number_dead_count = total_dead_missing
        else:
            number_missing_count += total_dead_missing - counted_terminal_events
    elif counted_terminal_events > total_dead_missing:
        total_dead_missing = counted_terminal_events

    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Article title", "Cause of Death", "Location of Death", "Location_of_death"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Country of Origin", "Information Source", "URL"], is_missing))

    collective_event_uri = None
    if total_dead_missing >= 2:
        collective_event_uri = DATA["iom_CollectiveEvent_%d" % (idx+1)]
        if str(collective_event_uri) not in created_collective_events:
            g.add((collective_event_uri, RDF.type, F.CollectiveEvent))
            g.add((collective_event_uri, RDFS.label, Literal(f"Événement collectif {idx+1}")))
            g.add((collective_event_uri, PROP_totalDeadAndMissing, Literal(total_dead_missing, datatype=XSD.integer)))

            survivors_val = (
                parse_int_value(row.get("Number of Survivors", ""))
                or parse_int_value(row.get("Number of survivors", ""))
                or parse_int_value(row.get("Nombre de survivants", ""))
            )
            number_dead_val = number_dead_count
            number_missing_val = number_missing_count

            if survivors_val is not None:
                g.add((collective_event_uri, PROP_numberOfSurvivors, Literal(survivors_val, datatype=XSD.integer)))
            if number_dead_val is not None:
                g.add((collective_event_uri, PROP_numberDead, Literal(number_dead_val, datatype=XSD.integer)))
            if number_missing_val is not None:
                g.add((collective_event_uri, PROP_numberMissing, Literal(number_missing_val, datatype=XSD.integer)))

            created_collective_events[str(collective_event_uri)] = collective_event_uri
            count_collective_events += 1

    person_event_pairs = []
    event_uris = []
    for death_idx in range(number_dead_count):
        person_pos = len(person_event_pairs) + 1
        person_uri = DATA[f"iom_Person_{idx+1}_{person_pos}"]
        if total_dead_missing == 1 and number_dead_count == 1 and number_missing_count == 0:
            event_uri = DATA[f"iom_Death_{idx+1}"]
        else:
            event_uri = DATA[f"iom_Death_{idx+1}_{death_idx+1}"]

        g.add((person_uri, RDF.type, PERSON_CLASS))
        g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
        g.add((event_uri, RDF.type, DEATH_INJURY_EVENT_CLASS))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))
        created_death_events[str(event_uri)] = event_uri
        person_event_pairs.append((person_uri, event_uri))
        event_uris.append(event_uri)
        count_person += 1
        count_death_events += 1

    for missing_idx in range(number_missing_count):
        person_pos = len(person_event_pairs) + 1
        person_uri = DATA[f"iom_Person_{idx+1}_{person_pos}"]
        event_uri = DATA[f"iom_Missing_{idx+1}_{missing_idx+1}"]

        g.add((person_uri, RDF.type, PERSON_CLASS))
        g.add((event_uri, RDF.type, MISSING_EVENT_CLASS))
        g.add((event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, F.group, collective_event_uri))
        person_event_pairs.append((person_uri, event_uri))
        event_uris.append(event_uri)
        count_person += 1
        count_missing_events += 1

    # NOMS (non présent dans ce jeu de données)
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
    age_from_text = None
    age_interval = None
    try:
        if age_val is not None and age_val != "" and not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
            age_from_text = age_val
        else:
            age_from_text = parse_age_from_text(row.get("Article title", ""), row.get("Cause of Death", ""), row.get("Location of Death", ""))
            if age_from_text is None:
                age_interval = parse_age_interval_from_text(row.get("Article title", ""), row.get("Cause of Death", ""), row.get("Location of Death", ""))
    except Exception:
        age_from_text = None
        age_interval = None

    if age_from_text is not None:
        for pair_idx, (person_uri, _) in enumerate(person_event_pairs, start=1):
            age_node = create_age_node(g, age_from_text, row_index=(idx * 1000) + pair_idx)
            if age_node:
                g.add((person_uri, PROP_hasAgeLink, age_node))
                for age_literal in g.objects(age_node, F.hasAge):
                    g.add((person_uri, F.hasAge, age_literal))
    elif age_interval is not None:
        for pair_idx, (person_uri, _) in enumerate(person_event_pairs, start=1):
            age_interval_node = create_age_interval_node(g, age_interval, row_index=(idx * 1000) + pair_idx)
            if age_interval_node is not None:
                g.add((person_uri, PROP_hasAgeInterval, age_interval_node))

    # SEXE
    n_fem = parse_int_value(row.get("Number of Females", "")) or 0
    n_mal = parse_int_value(row.get("Number of Males", "")) or 0
    if n_fem > 0 and n_mal == 0:
        for person_uri, _ in person_event_pairs:
            g.set((person_uri, PROP_gender, GENDER_URIS["female"]))
    elif n_mal > 0 and n_fem == 0:
        for person_uri, _ in person_event_pairs:
            g.set((person_uri, PROP_gender, GENDER_URIS["male"]))

    # LIEU DE NAISSANCE
    birth_countries = ensure_country_nodes(g, row.get("Country of Origin", ""))
    for birth_country in birth_countries:
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES (non présent dans ce jeu de données)
    comment_cdb = row.get("Commentaire CDB", "") or row.get("Commentaire_CDB", "")
    if comment_cdb and not is_missing(comment_cdb):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))
    
    comment_sb = row.get("Commentaire SB", "") or row.get("Commentaire_SB", "")
    if comment_sb and not is_missing(comment_sb):
        for person_uri, _ in person_event_pairs:
            g.add((person_uri, PROP_hasComment, Literal(str(comment_sb).strip())))

    # Injury doit etre modele en ante-mortem / ante-disparition par rapport a une personne existante.
    injury_anchor_pairs = person_event_pairs

    injury_count = estimate_injury_count_from_text(
        row.get("Article title", ""),
        row.get("Cause of Death", ""),
        row.get("Location of Death", ""),
    )
    injury_event_pairs = []
    for injury_idx in range(min(injury_count, len(injury_anchor_pairs))):
        injury_uri = DATA[f"iom_InjuryEvent_{idx+1}_{injury_idx+1}"]
        injury_person_uri, injury_anchor_event_uri = injury_anchor_pairs[injury_idx]
        g.add((injury_uri, RDF.type, INJURY_EVENT_CLASS))
        g.add((injury_uri, RDF.type, F.IndividualEvent))
        g.add((injury_person_uri, PROP_composedOf, injury_uri))
        if injury_anchor_event_uri is not None:
            g.add((injury_uri, PROP_temporal_before, injury_anchor_event_uri))
            g.add((injury_anchor_event_uri, PROP_temporal_after, injury_uri))
        if collective_event_uri is not None:
            g.add((injury_uri, F.group, collective_event_uri))
        injury_event_pairs.append((injury_person_uri, injury_uri))

    # Utiliser le premier evenement individuel comme ancrage de ligne pour les proprietes aval.
    event_uri = event_uris[0]

    for ev_pos, ev_uri in enumerate(event_uris):
        if ev_pos < number_dead_count:
            g.add((ev_uri, PROP_hasVictimState, THES_victim_dead))
        else:
            g.add((ev_uri, PROP_hasVictimState, THES_victim_missing))

    additional_counts = add_additional_typed_events(
        g,
        person_event_pairs,
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "iom",
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

    # DATE DE DÉCÈS (Website Date)
    date_mort_val = row.get("Website Date", "") or row.get("Website Date ", "")
    weekday_name_fallback = infer_day_of_week_name(
        date_mort_val,
        row.get("Article title", ""),
        row.get("Cause of Death", ""),
    )
    if date_mort_val and not is_missing(date_mort_val):
        try:
            # Parser la date - essayer plusieurs formats
            date_str = str(date_mort_val).strip()

            # Attribut métier "Date du site" (valeur texte source)
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_dateDuSite, Literal(date_str)))

            parsed_date = None
            
            # Essayer format ISO (YYYY-MM-DD)
            try:
                parsed_date = datetime.strptime(date_str, "%Y-%m-%d")
            except ValueError:
                pass
            
            # Essayer format avec heure (YYYY-MM-DD HH:MM:SS)
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str.split()[0], "%Y-%m-%d")
                except (ValueError, IndexError):
                    pass
            
            # Essayer format DD/MM/YYYY
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str, "%d/%m/%Y")
                except ValueError:
                    pass
            
            # Essayer format DD-MM-YYYY
            if not parsed_date:
                try:
                    parsed_date = datetime.strptime(date_str, "%d-%m-%Y")
                except ValueError:
                    pass
            
            # Si date validée, ajouter au graphe (format xsd:date YYYY-MM-DD)
            if parsed_date:
                date_iso = parsed_date.strftime("%Y-%m-%d")
                weekday_name = infer_day_of_week_name(date_iso)
                for ev_uri in event_uris:
                    g.add((ev_uri, TIME.inXSDDate, Literal(date_iso, datatype=XSD.date)))
                    if weekday_name:
                        g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name]))
                        g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                        g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
            elif weekday_name_fallback:
                for ev_uri in event_uris:
                    g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name_fallback]))
                    g.add((TIME[weekday_name_fallback], RDF.type, TIME.DayOfWeek))
                    g.add((TIME[weekday_name_fallback], RDFS.label, Literal(weekday_name_fallback, lang="en")))
        except Exception as e:
            print(f"Erreur parsing date pour ligne {idx+1}: {date_mort_val} - {e}")
    elif weekday_name_fallback:
        for ev_uri in event_uris:
            g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name_fallback]))
            g.add((TIME[weekday_name_fallback], RDF.type, TIME.DayOfWeek))
            g.add((TIME[weekday_name_fallback], RDFS.label, Literal(weekday_name_fallback, lang="en")))

    # DATE DE MORT = Reported Month + Reported Year (ex. "January 2010")
    reported_month_val = row.get("Reported Month", "") or row.get("Reported month", "")
    reported_year_val = row.get("Reported Year", "") or row.get("Reported year", "")
    if not is_missing(reported_month_val) and not is_missing(reported_year_val):
        date_de_mort_text = f"{str(reported_month_val).strip()} {str(reported_year_val).strip()}"
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_dateDeMort, Literal(date_de_mort_text)))

    # CERTIFICAT DE DÉCÈS
    acte_deces_val = row.get("Death_certificate", "") or row.get("death_certificate", "")
    if acte_deces_val and not is_missing(acte_deces_val):
        certificate_uri = DATA["DeathCertificate_%d" % (idx+1)]
        g.add((certificate_uri, RDF.type, DEATH_CERTIFICATE_CLASS))
        g.add((event_uri, PROP_certificate, certificate_uri))
        g.add((certificate_uri, PROP_hasIdCertificate, Literal(str(acte_deces_val).strip())))
        count_death_certificates += 1

    # frontiere_EX (non présent dans ce jeu de données)
    front_ex = row.get("Frontiere_EX", "") or row.get("frontiere_EX", "") or row.get("frontiere_EX".lower(), "")
    if not is_missing(front_ex):
        cnode = ensure_country_node(g, str(front_ex).strip())
        if cnode:
            g.add((event_uri, PROP_borderOUT, cnode))

    # frontiere_IN (non présent dans ce jeu de données)
    front_in = row.get("Frontiere_IN", "") or row.get("frontiere_IN", "") or row.get("frontiere_IN".lower(), "")
    if not is_missing(front_in):
        cnode = ensure_country_node(g, str(front_in).strip())
        if cnode:
            g.add((event_uri, PROP_borderIN, cnode))

    location_of_death = (
        row.get("Location of Death", "")
        or row.get("Location_of_death", "")
        or row.get("Country", "")
        or row.get("country", "")
    )

    # GEO - priorité au champ combiné IOM Coordinates (lat, lon), puis LAT/LONG,
    # puis géocodage du Location of Death si rien n'est disponible.
    iom_coordinates_val = (
        row.get("IOM Coordinates Getallen omdraaien, onderste eerst in FM  ", "")
        or row.get("IOM Coordinates Getallen omdraaien, onderste eerst in FM", "")
    )
    lat = row.get("LAT", "") or row.get("lat", "") or row.get("Coord_Lat_deces", "") or row.get("Coord_lat_deces", "")
    lon = row.get("LONG", "") or row.get("long", "") or row.get("Coord_Long_deces", "") or row.get("Coord_long_deces", "")
    geometry_added = False
    try:
        lat_f = None
        lon_f = None
        death_geocoded_fallback = False

        if not is_missing(iom_coordinates_val):
            lat_f, lon_f = parse_coordinate_pair(iom_coordinates_val)

        if (lat_f is None or lon_f is None) and not is_missing(lat) and not is_missing(lon):
            lat_f = parse_coordinate_value(lat)
            lon_f = parse_coordinate_value(lon)

        if (lat_f is None or lon_f is None) and not is_missing(location_of_death):
            lat_f, lon_f = geocode_location(str(location_of_death).strip())
            if lat_f is not None and lon_f is not None:
                death_geocoded_fallback = True
                print(f"Géocodé depuis 'Location of Death' '{location_of_death}' -> ({lat_f}, {lon_f})")

        if lat_f is not None and lon_f is not None and math.isfinite(lat_f) and math.isfinite(lon_f):
            # Vérifier si les coordonnées sont suspectes
            is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
            if is_suspicious:
                print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon_f}, {lat_f}")
            else:
                wkt = build_wkt_for_location_precision(location_of_death, lat_f, lon_f, death_geocoded_fallback)
                for ev_pos, ev_uri in enumerate(event_uris, start=1):
                    geometry_uri = DATA[f"iom_geometry_{idx+1}_{ev_pos}"]
                    g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                    g.add((geometry_uri, RDF.type, GEO.Geometry))
                    g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
                    g.add((geometry_uri, F.hasPrecision, Literal(not death_geocoded_fallback, datatype=XSD.boolean)))
                    if death_geocoded_fallback and location_of_death and not is_missing(location_of_death):
                        g.add((ev_uri, F.lieu, Literal(str(location_of_death).strip())))
                geometry_added = True
    except Exception:
        geometry_added = False

    location_of_death = (
        row.get("Location of Death", "")
        or row.get("Location_of_death", "")
        or row.get("Country", "")
        or row.get("country", "")
    )
    # Pays: on conserve uniquement le pays de naissance (Country of Origin).

    # TRANSPORT
    transport_text_candidates = [
        row.get("Article title", ""),
        row.get("Location_of_death", ""),
        row.get("Location of Death", ""),
        row.get("Cause of Death", ""),
    ]
    transport_token = None
    for candidate in transport_text_candidates:
        transport_token = detect_transport_from_text(candidate)
        if transport_token:
            break

    if transport_token:
        transport_uri = DATA[f"iom_Transport_{transport_token}_{idx+1}"]
        if str(transport_uri) not in created_transports:
            g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
            g.add((transport_uri, PROP_transportName, Literal(transport_token)))
            created_transports[str(transport_uri)] = transport_uri
            count_transports += 1

        for ev_uri in event_uris:
            g.add((transport_uri, PROP_usedIn, ev_uri))

    # Le regroupement collectif est gere strictement via "Total Dead and Missing" ci-dessus.

    # RAPATRIEMENT
    enterrement_text = str(row.get("Article title", "")).strip()
    if ("repatriated" in norm(enterrement_text) or "repatriated" in norm(enterrement_text) or "repatriation" in norm(enterrement_text) or "repatriation" in norm(enterrement_text)) and "?" not in enterrement_text:
        for pair_idx, (person_uri, terminal_event_uri) in enumerate(person_event_pairs, start=1):
            repatriation_event_uri = DATA[f"iom_Repatriation_{idx+1}_{pair_idx}"]
            g.add((repatriation_event_uri, RDF.type, CORPSE_REPATRIATION_CLASS))
            g.add((repatriation_event_uri, RDF.type, F.IndividualEvent))
            g.add((person_uri, PROP_composedOf, repatriation_event_uri))
            g.add((terminal_event_uri, TEMP.before, repatriation_event_uri))
            g.add((repatriation_event_uri, PROP_temporal_after, terminal_event_uri))
            for birth_country in birth_countries:
                g.add((repatriation_event_uri, PROP_targetCountry, birth_country))
            count_repatriation += 1

    # INHUMATION
    comm_enterrement = row.get("Article title ", "") or row.get("Location of Death ", "")
    comm_enterrement_norm = norm(comm_enterrement)
    if (
        comm_enterrement
        and not is_missing(comm_enterrement)
        and any(keyword in comm_enterrement_norm for keyword in ["buried", "burial", "funeral", "interment"])
    ):
        # Récupérer les coordonnées existantes (non présents dans ce jeu de données)
        lat_ent = row.get("Coord_Lat_enterrement", "") or row.get("Coord_lat_enterrement", "")
        lon_ent = row.get("Coord_Long_enterrement", "") or row.get("Coord_long_enterrement", "")
        
        lat_e = None
        lon_e = None
        inhumation_geocoded_fallback = False
        
        # Essayer d'utiliser les coordonnées existantes
        try:
            if not is_missing(lat_ent) and not is_missing(lon_ent):
                lat_e = parse_coordinate_value(lat_ent)
                lon_e = parse_coordinate_value(lon_ent)
                if lat_e is None or lon_e is None or not (math.isfinite(lat_e) and math.isfinite(lon_e)):
                    lat_e = None
                    lon_e = None
        except Exception:
            lat_e = None
            lon_e = None
        
        # Si pas de coordonnées, géocoder Comm_enterrement
        if lat_e is None or lon_e is None:
            lat_e, lon_e = geocode_location(str(comm_enterrement).strip())
            if lat_e is not None and lon_e is not None:
                inhumation_geocoded_fallback = True
                print(f"Géocodé '{comm_enterrement}' -> ({lat_e}, {lon_e})")

        for pair_idx, (person_uri, terminal_event_uri) in enumerate(person_event_pairs, start=1):
            inhumation_event_uri = DATA[f"InhumationEvent_{idx+1}_{pair_idx}"]
            if (inhumation_event_uri, None, None) not in g:
                g.add((inhumation_event_uri, RDF.type, F.Inhumation))
                g.add((inhumation_event_uri, RDF.type, F.IndividualEvent))

            g.add((person_uri, PROP_composedOf, inhumation_event_uri))

            if lat_e is not None and lon_e is not None:
                is_suspicious, reason = is_suspicious_coordinate(lat_e, lon_e)
                if is_suspicious:
                    print(f"  ⚠️  Coordonnée suspecte ignorée pour inhumation ({reason}): {lon_e}, {lat_e}")
                else:
                    wkt_ent = build_wkt_for_location_precision(comm_enterrement, lat_e, lon_e, False)
                    geometry_inhumation_uri = DATA[f"iom_geometry_inhumation_{idx+1}_{pair_idx}"]
                    g.add((inhumation_event_uri, GEO.hasGeometry, geometry_inhumation_uri))
                    g.add((geometry_inhumation_uri, RDF.type, GEO.Geometry))
                    g.add((geometry_inhumation_uri, GEO.asWKT, Literal(wkt_ent, datatype=GEO.wktLiteral)))
                    g.add((geometry_inhumation_uri, F.hasPrecision, Literal(not inhumation_geocoded_fallback, datatype=XSD.boolean)))
                    if inhumation_geocoded_fallback and comm_enterrement and not is_missing(comm_enterrement):
                        g.add((inhumation_event_uri, F.lieu, Literal(str(comm_enterrement).strip())))

            g.add((terminal_event_uri, TEMP.before, inhumation_event_uri))
            count_inhumation += 1
            g.add((inhumation_event_uri, PROP_temporal_after, terminal_event_uri))
    # SOURCE
    source_val = row.get("URL", "")
    source_str = str(source_val).strip() if source_val is not None else ""
    has_valid_url = (not is_missing(source_str)) and source_str.lower().startswith('http')

    article_title_val = (
        row.get("Article title", "")
        or row.get("Article title ", "")
        or row.get("Article title  ", "")
        or row.get("Title", "")
    )
    has_article_title = article_title_val and not is_missing(article_title_val)

    info_source_val = row.get("Information Source", "")
    has_info_source = info_source_val and not is_missing(info_source_val)

    # Créer une source si au moins un des champs est disponible
    if has_valid_url or has_article_title or has_info_source:
        source_uri = DATA["iom_Source_%d" % (idx+1)]
        
        # Type de source selon "Information Source"
        source_type_class = get_source_type_class(
            " ".join(
                filter(
                    None,
                    [
                        str(info_source_val).strip() if has_info_source else "",
                        str(article_title_val).strip() if has_article_title else "",
                    ],
                )
            )
        )
        g.add((source_uri, RDF.type, F.Source))
        g.add((source_uri, RDF.type, source_type_class))

        # rdfs:label = Information Source
        if has_info_source:
            g.add((source_uri, RDFS.label, Literal(str(info_source_val).strip())))
        
        # frontlet:hasComment = Article title
        if has_article_title:
            article_title_text = str(article_title_val).strip()
            g.add((source_uri, PROP_hasComment, Literal(article_title_text)))
        
        # frontlet:hasWebLink = URL
        if has_valid_url:
            g.add((source_uri, PROP_hasWebLink, Literal(source_str)))
        elif has_article_title or has_info_source:
            # Meme sans URL, ajouter quand meme le lien vers la source
            g.add((source_uri, PROP_hasWebLink, Literal("")))

        for ev_uri in event_uris:
            g.add((ev_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

    # CAUSE DE DÉCÈS - Créer instance DeathCause et attacher à l'événement
    cause_deces_val = row.get("Cause of Death", "") or row.get("Cause de décès", "")
    if cause_deces_val and not is_missing(cause_deces_val):
        _, mapped_label, _ = match_death_cause(cause_deces_val, mapping_dict, thesaurus_map)
        cause_label = mapped_label if mapped_label else cause_deces_val
        death_cause_instance = create_or_get_death_cause_instance(g, cause_label)
        if death_cause_instance:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, death_cause_instance))
            count_cause_matched += 1
        else:
            # Repli vers une valeur litterale si le slug est vide
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, Literal(str(cause_deces_val).strip())))
            count_cause_literal += 1
        
        # Détection d'accidents de circulation
        is_accident, transport_type = detect_traffic_accident_and_transport(cause_deces_val)
        if is_accident:
            count_traffic_accidents += 1
            if transport_type:
                count_transport_identified += 1

        # NATURE DE DÉCÈS — depuis la colonne Nature du CSV de mapping
        nature_label = mapping_nature.get(norm(cause_deces_val))
        if nature_label:
            nature_instance = create_or_get_death_nature_instance(g, nature_label)
            if nature_instance is not None:
                for ev_uri in event_uris:
                    g.add((ev_uri, PROP_hasDeathNature, nature_instance))

# --------------------- Resume et sortie ------------------
count_geom_propagated = propagate_geometry_to_sibling_events(g, F, GEO, RDF, Literal, "iom")
count_event_country_from_geometry = add_event_country_from_geometry(g, F, DATA, GEO, RDF, RDFS, Literal, "iom")
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "="*60)
print("Import IOM complete.")
print("="*60)
print(f"Rows processed (persons): {count_person}")
print(f"Death events created: {count_death_events}")
print(f"Missing events created: {count_missing_events}")
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
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

