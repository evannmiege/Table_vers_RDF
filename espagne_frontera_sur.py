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
CSV_PATH = "espagne_frontera_sur/espagne_frontera_sur.csv"
OUTPUT_TTL = "espagne_frontera_sur/frontlet_import_output.ttl"
MAPPING_PATH = "espagne_frontera_sur/mappingEspagneFronteraSurThesaurusCauseMort.csv"  # Fichier de mapping CSV (optionnel)

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
geolocator = Nominatim(user_agent="frontlet_alpes_geocoder")
MAX_GEOCODING_CALLS = 10
geocoding_calls_count = 0

def geocode_location(location_name, max_retries=3):
    """
    Géocode un nom de lieu et retourne (latitude, longitude) ou (None, None).
    Cherche d'abord un cimetière, sinon utilise le centroïde de la ville.
    """
    global geocoding_calls_count

    if geocoding_calls_count >= MAX_GEOCODING_CALLS:
        return None, None

    if is_missing(location_name):
        return None, None

    geocoding_calls_count += 1
    
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

THES_male = find_thesaurus_term_by_prefLabel_fr(g_ref, "male") or find_thesaurus_term_by_prefLabel_fr(g_ref, "homme") or T.male
THES_female = find_thesaurus_term_by_prefLabel_fr(g_ref, "female") or find_thesaurus_term_by_prefLabel_fr(g_ref, "femme") or T.female
THES_human = find_thesaurus_term_by_prefLabel_fr(g_ref, "human") or find_thesaurus_term_by_prefLabel_fr(g_ref, "humain") or T.human
MISSING_EVENT_CLASS = F.Missing
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation", "CorpseRepatriation"])

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
    person_uri = DATA["alpes_Person_%d" % (idx+1)]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1

    embark_uri = None
    repatriation_event_uri = None
    inhumation_event_uri = None

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

    # AGE
    age_node = None
    age_val = row.get("Age", "")
    try:
        if age_val is not None and age_val != "" and not is_missing(age_val) and re.match(r"^\s*\d+(\.\d+)?\s*$", str(age_val)):
            age_node = create_age_node(g, age_val)
            if age_node:
                g.add((person_uri, PROP_hasAgeLink, age_node))
    except Exception:
        pass

    # SEXE (inference textuelle depuis NOTA)
    gender_text = norm(row.get("NOTA", "") or row.get("Nota", "") or row.get("Description", ""))
    if gender_text and not is_missing(gender_text):
        if any(k in gender_text for k in (" hombre ", "hombre", " varon", "varón", " male ", " man ", " boy ", " nino", "niño")):
            if THES_male is not None:
                g.add((person_uri, F.gender, THES_male))
            else:
                g.add((person_uri, F.gender, Literal("male")))
        elif any(k in gender_text for k in (" mujer ", "mujer", " female ", " woman ", " girl ", " nina", "niña")):
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
        g.add((person_uri, PROP_birthPlace, birth_country))

    # COMMENTAIRES
    comment_cdb = row.get("Commentaire CDB", "") or row.get("Commentaire_CDB", "")
    if comment_cdb and not is_missing(comment_cdb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_cdb).strip())))
    
    comment_sb = row.get("Commentaire SB", "") or row.get("Commentaire_SB", "")
    if comment_sb and not is_missing(comment_sb):
        g.add((person_uri, PROP_hasComment, Literal(str(comment_sb).strip())))

    # EVENEMENTS INDIVIDUELS DECES / BLESSURE (MUERTO / DESAPARECIDO)
    muerto_count = parse_int_value(row.get("MUERTO", ""))
    desaparecido_count = parse_int_value(row.get("DESAPARECIDO", ""))
    muerto_count = max(0, muerto_count or 0)
    desaparecido_count = max(0, desaparecido_count or 0)
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Cause_deces", "LUGAR", "ZONA", "Pays_mort"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Commentaire CDB", "Commentaire SB"], is_missing))

    event_uris = []

    # n evenements typés Death (sous-classe de DeathInjury)
    for ev_pos in range(muerto_count):
        # Une URI basee sur la ligne + le rang garantit des IDs stables lors des relances.
        event_uri = DATA[f"espagne_Death_{idx+1}_{ev_pos+1}"]
        if str(event_uri) not in created_death_events:
            g.add((event_uri, RDF.type, DEATH_EVENT_CLASS))
            g.add((event_uri, RDF.type, DEATH_INJURY_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_death_events[str(event_uri)] = event_uri
            count_death_events += 1
        g.add((person_uri, PROP_composedOf, event_uri))
        event_uris.append(event_uri)

    # n evenements typés Missing
    for ev_pos in range(desaparecido_count):
        event_uri = DATA[f"espagne_Missing_{idx+1}_{ev_pos+1}"]
        if str(event_uri) not in created_death_events:
            g.add((event_uri, RDF.type, MISSING_EVENT_CLASS))
            g.add((event_uri, RDF.type, F.IndividualEvent))
            created_death_events[str(event_uri)] = event_uri
            count_death_events += 1
        g.add((person_uri, PROP_composedOf, event_uri))
        event_uris.append(event_uri)

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, ev_uri) for ev_uri in event_uris],
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

    # GEO depuis LUGAR, repli sur ZONA quand LUGAR est absent
    lugar_val = row.get("LUGAR", "") or row.get("lugar", "")
    zona_val = row.get("ZONA", "") or row.get("zona", "")
    geocode_text = None
    if not is_missing(lugar_val):
        geocode_text = str(lugar_val).strip()
    elif not is_missing(zona_val):
        geocode_text = str(zona_val).strip()

    geometry_added = False
    try:
        if geocode_text:
            lat_f, lon_f = geocode_location(geocode_text)
            if lat_f is not None and lon_f is not None and math.isfinite(lat_f) and math.isfinite(lon_f):
                # Vérifier si les coordonnées sont suspectes
                is_suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
                if is_suspicious:
                    print(f"  ⚠️  Coordonnée suspecte ignorée ({reason}): {lon_f}, {lat_f}")
                else:
                    wkt = f"POINT({lon_f} {lat_f})"
                    for ev_pos, ev_uri in enumerate(event_uris, start=1):
                        geometry_uri = DATA[f"espagne_geometry_{idx+1}_{ev_pos}"]
                        g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                        g.add((geometry_uri, RDF.type, GEO.Geometry))
                        g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
                    geometry_added = bool(event_uris)
    except Exception:
        geometry_added = False

    pays_mort = row.get("Pays_mort", "") or row.get("pays_mort", "") or row.get("Pays_mort".lower(), "")
    if (not geometry_added) and not is_missing(pays_mort) and event_uri is not None:
        country_node = ensure_country_node(g, str(pays_mort).strip())
        if country_node:
            for ev_uri in event_uris:
                g.add((ev_uri, F.paysMort, country_node))

    # TRANSPORT
    transport_val = row.get("transport", "") or row.get("Transport", "") or row.get("transport".lower(), "")
    if not is_missing(transport_val):
        t_norm = norm(transport_val)
        # Transports humains (pas d'événement d'embarquement)
        is_human_transport = any(keyword in t_norm for keyword in ["marche", "nage", "pied", "humain"])
        
        if is_human_transport:
            if THES_human is not None:
                for ev_uri in event_uris:
                    g.add((ev_uri, F.transportMode, THES_human))
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
                    for ev_uri in event_uris:
                        g.add((ev_uri, PROP_transportType, transport_uri))

                    # Créer un événement d'embarquement uniquement pour les transports non-humains
                    embark_uri = DATA["EmbarkEvent_%d_%s" % (idx+1, slug)]
                    if (embark_uri, None, None) not in g:
                        g.add((embark_uri, RDF.type, EMBARK_EVENT_CLASS))
                    g.add((embark_uri, PROP_usedIn, transport_uri))
                    if event_uri is not None:
                        g.add((embark_uri, PROP_temporal_before, event_uri))
                        g.add((event_uri, PROP_temporal_after, embark_uri))
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

        for ev_uri in event_uris:
            g.add((ev_uri, F.group, collective_event_uri))
        if embark_uri is not None:
            g.add((embark_uri, F.group, collective_event_uri))

    # RAPATRIEMENT
    enterrement_text = str(row.get("Enterrement", "")).strip()
    if ("rapatrié" in norm(enterrement_text) or "rapatriement" in norm(enterrement_text)) and "?" not in enterrement_text:
        repatriation_event_uri = DATA["alpes_Repatriation_%d" % (idx+1)]
        g.add((repatriation_event_uri, RDF.type, F.Repatriation))
        g.add((repatriation_event_uri, RDF.type, F.IndividualEvent))
        g.add((person_uri, PROP_composedOf, repatriation_event_uri))
        if event_uri is not None:
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
            g.add((inhumation_event_uri, RDF.type, F.IndividualEvent))
        
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
                geometry_inhumation_uri = DATA[f"alpes_geometry_inhumation_{idx+1}"]
                g.add((inhumation_event_uri, GEO.hasGeometry, geometry_inhumation_uri))
                g.add((geometry_inhumation_uri, RDF.type, GEO.Geometry))
                g.add((geometry_inhumation_uri, GEO.asWKT, Literal(wkt_ent, datatype=GEO.wktLiteral)))
        
        if event_uri is not None:
            g.add((event_uri, TEMP.before, inhumation_event_uri))
        count_inhumation += 1
        if event_uri is not None:
            g.add((inhumation_event_uri, PROP_temporal_after, event_uri))
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
        combined_source_text = " ".join(source_urls)
        source_category = infer_source_category_key(combined_source_text)
        SOURCE_SUBTYPE_MAP = {"family": F.Family, "media": F.Media, "civil_society": F.CivilSociety, "death_certificate": F.DeathCertificate, "official_document": F.OtherOfficialDocument}
        sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
        if sub_type:
            g.add((source_uri, RDF.type, sub_type))
        # Conserver un attribut hasWebLink par colonne source non vide.
        for url in source_urls:
            g.add((source_uri, PROP_hasWebLink, Literal(url)))
        for ev_uri in event_uris:
            g.add((ev_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

# --------------------- Resume et sortie ------------------
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
print("="*60)
print(f"Output written to: {OUTPUT_TTL}")

