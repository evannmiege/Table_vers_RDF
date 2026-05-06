import pandas as pd
from rdflib import Graph, Namespace, Literal, URIRef
from rdflib.namespace import RDF, RDFS, XSD, SKOS
from urllib.parse import quote
from datetime import datetime
import warnings
import os
from comparerCalaisUnited import build_calais_united_matches
import re
import pycountry
from geopy.geocoders import Nominatim
from geopy.exc import GeocoderTimedOut, GeocoderServiceError
import time
warnings.filterwarnings('ignore')

# Import du fichier CSV
print("Import du fichier Calaisborder20250324_semicolon.csv...")
df = pd.read_csv("c:/Users/bresra/Desktop/ontoSequenceEvenement/calais/Calaisborder20250324_semicolon.csv", 
                 sep=';', 
                 encoding='utf-8')

# Import des ontologies
print("\nImport des ontologies...")
g_onto = Graph()
g_thesaurus = Graph()

g_onto.parse("c:/Users/bresra/Desktop/ontoSequenceEvenement/frontletOnto.ttl", format='turtle')
g_thesaurus.parse("c:/Users/bresra/Desktop/ontoSequenceEvenement/frontletThesaurus.ttl", format='turtle')

print(f"Ontologie frontletOnto.ttl chargée: {len(g_onto)} triples")
print(f"Ontologie frontletThesaurus.ttl chargée: {len(g_thesaurus)} triples")

# Définition des namespaces
FRONTLET = Namespace("http://purl.org/frontierelethale/onto/")
FRONTLET_DATA = Namespace("http://data/frontlet/")
FRONTLET_THESAURUS = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")

# Création du graphe RDF pour l'export
g = Graph()
g.bind("frontlet", FRONTLET)
g.bind("frontlet_data", FRONTLET_DATA)
g.bind("frontlet_thesaurus", FRONTLET_THESAURUS)
g.bind("geo", GEO)
g.bind("time", TIME)
g.bind("rdf", RDF)
g.bind("rdfs", RDFS)
g.bind("xsd", XSD)
g.bind("skos", SKOS)

# ============================================================================
# FONCTIONS UTILITAIRES
# ============================================================================

# Initialiser le géocodeur
geolocator = Nominatim(user_agent="frontlet_calais_importer")
geocoding_cache = {}

def geocode_location(location_str, max_retries=2):
    """
    Géocode une localisation et retourne (lat, lon) ou (None, None) si échec.
    Utilise un cache pour éviter de répéter les requêtes.
    """
    if pd.isna(location_str) or str(location_str).strip() == '':
        return None, None
    
    location_str = str(location_str).strip()
    
    # Vérifier le cache
    if location_str in geocoding_cache:
        return geocoding_cache[location_str]
    
    # Essayer le géocodage avec retry
    for attempt in range(max_retries):
        try:
            time.sleep(1.1)  # Respecter le rate limit de Nominatim (1 req/sec)
            location = geolocator.geocode(location_str, timeout=10)
            if location:
                lat, lon = location.latitude, location.longitude
                geocoding_cache[location_str] = (lat, lon)
                print(f"  ✓ Géocodage réussi: '{location_str}' -> ({lon}, {lat})")
                return lat, lon
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                time.sleep(2)
                continue
        except GeocoderServiceError:
            break
        except Exception as e:
            print(f"  ⚠️  Erreur géocodage: {e}")
            break
    
    # Échec du géocodage
    geocoding_cache[location_str] = (None, None)
    return None, None

def parse_calais_date(date_str):
    """Parse la date au format YYYYMMDD et retourne un objet datetime"""
    if pd.isna(date_str) or date_str == '':
        return None
    try:
        date_str = str(date_str).strip()
        if len(date_str) >= 8:
            year = date_str[:4]
            month = date_str[4:6]
            day = date_str[6:8]
            return datetime.strptime(f"{year}-{month}-{day}", "%Y-%m-%d")
    except:
        pass
    return None

def parse_age(age_str):
    """
    Parse le champ age et retourne un tuple (age_value, is_precise)
    Exemples: ">30" -> (30, False), "25" -> (25, True), "25-30" -> (27, False)
    """
    if pd.isna(age_str) or str(age_str).strip() == '':
        return None, None
    
    age_str = str(age_str).strip()
    
    # Cas: >30, <25, etc.
    if age_str.startswith('>') or age_str.startswith('<'):
        try:
            age_value = int(age_str[1:])
            return age_value, False
        except:
            return None, None
    
    # Cas: 25-30
    if '-' in age_str:
        try:
            parts = age_str.split('-')
            if len(parts) == 2:
                age_min = int(parts[0])
                age_max = int(parts[1])
                age_value = (age_min + age_max) // 2
                return age_value, False
        except:
            return None, None
    
    # Cas: 25 (ou "25 (né le ...)")
    try:
        # Extraire le premier nombre
        match = re.match(r'(\d+)', age_str)
        if match:
            age_value = int(match.group(1))
            return age_value, True
    except:
        pass
    
    return None, None

def clean_string_for_uri(s):
    """Nettoie une chaîne pour l'utiliser dans une URI"""
    if pd.isna(s):
        return ""
    s = str(s).strip()
    s = s.replace(' ', '_')
    s = s.replace('/', '_')
    s = s.replace('\\', '_')
    s = s.replace('?', '')
    s = s.replace('#', '')
    s = s.replace('&', '_')
    s = s.replace('=', '_')
    s = s.replace(';', '_')
    s = s.replace(',', '_')
    return quote(s, safe='_-')

def find_by_label(graph, search, props=(RDFS.label, SKOS.prefLabel)):
    if search is None or str(search).strip() == "":
        return None
    s_norm = str(search).strip().lower()
    for p in props:
        for s, _, o in graph.triples((None, p, None)):
            if str(o).strip().lower() == s_norm:
                return s
    for p in props:
        for s, _, o in graph.triples((None, p, None)):
            if s_norm in str(o).strip().lower():
                return s
    return None

def ensure_country_node(country_value):
    """Crée ou récupère un noeud Country à partir d'un libellé, avec résolution ISO."""
    if pd.isna(country_value) or str(country_value).strip() == '':
        return None

    val = str(country_value).strip()
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
        country_uri = FRONTLET_DATA[f"calais_country_{iso3.upper()}"]
        if (country_uri, None, None) not in g:
            g.add((country_uri, RDF.type, FRONTLET.Country))
            en_label = Literal(getattr(cc, "name", val), lang="en")
            if (country_uri, RDFS.label, en_label) not in g:
                g.add((country_uri, RDFS.label, en_label))
            g.add((country_uri, FRONTLET.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            g.add((country_uri, FRONTLET.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            g.add((country_uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return country_uri

    candidate = find_by_label(g, country_value)
    if candidate:
        return candidate

    slug = re.sub(r'[^a-z0-9_]', '_', val.lower())
    slug = re.sub(r'_+', '_', slug).strip('_')
    if slug == '':
        return None

    country_uri = FRONTLET_DATA[f"calais_country_{slug}"]
    if (country_uri, None, None) not in g:
        g.add((country_uri, RDF.type, FRONTLET.Country))
        g.add((country_uri, RDFS.label, Literal(val)))
    return country_uri

def find_gender_in_thesaurus(gender_code):
    """
    Trouve l'URI du genre dans le thesaurus
    H -> masculin (male)
    F -> féminin (female)
    """
    if pd.isna(gender_code) or str(gender_code).strip() == '':
        return None
    
    gender_code = str(gender_code).strip().upper()
    
    if gender_code == 'H':
        return FRONTLET_THESAURUS.male
    elif gender_code == 'F':
        return FRONTLET_THESAURUS.female
    
    return None

def find_death_cause_in_thesaurus(cause_fr):
    """
    Trouve l'URI de la cause de mort dans le thesaurus à partir du label français
    """
    if pd.isna(cause_fr) or str(cause_fr).strip() == '':
        return None
    
    cause_fr = str(cause_fr).strip().lower()
    
    # Mapping des causes de mort (label français -> URI thesaurus)
    cause_mapping = {
        'noyade': FRONTLET_THESAURUS.drowning,
        'asphyxie': FRONTLET_THESAURUS.asphyxia,
        'suicide': FRONTLET_THESAURUS.suicide,
        'homicide': FRONTLET_THESAURUS.homicide,
        'accident de route lié au passage': FRONTLET_THESAURUS.roadAccident,  # À vérifier
        'pendaison': FRONTLET_THESAURUS.hanging,
        'électrocution': FRONTLET_THESAURUS.electrocution,
        'épuisement': FRONTLET_THESAURUS.exhaustion,
    }
    
    return cause_mapping.get(cause_fr)

def create_age_interval_from_minor(minor_value, person_id):
    """
    Crée un objet ageInterval basé sur la colonne 'minor' (Y/N)
    Y -> intervalle 0 à 17 (enfant)
    N -> intervalle 18 à 150 (adulte)
    Retourne l'URI de l'âge ou None
    """
    if pd.isna(minor_value) or str(minor_value).strip() == '':
        return None
    
    minor_value = str(minor_value).strip().upper()
    
    age_uri = FRONTLET_DATA[f"calais_age_{person_id}"]
    g.add((age_uri, RDF.type, FRONTLET.AgeInterval))
    
    if minor_value == 'Y':
        # Enfant: 0 à 17 ans
        g.add((age_uri, FRONTLET.hasAgeMin, Literal(0, datatype=XSD.integer)))
        g.add((age_uri, FRONTLET.hasAgeMax, Literal(17, datatype=XSD.integer)))
    elif minor_value == 'N':
        # Adulte: 18 à 150 ans
        g.add((age_uri, FRONTLET.hasAgeMin, Literal(18, datatype=XSD.integer)))
        g.add((age_uri, FRONTLET.hasAgeMax, Literal(150, datatype=XSD.integer)))
    else:
        return None
    
    g.add((age_uri, FRONTLET.hasPrecision, Literal(False, datatype=XSD.boolean)))
    return age_uri

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
    
    # PRIORITÉ: Coordonnées aberrantes avec lon ~ 1.80 et lat > 53 (zone incorrecte pour Calais)
    # Cette règle est vérifiée en premier et surpasse toutes les autres
    # Élargie pour capturer toutes les coordonnées suspectes dans la zone Calais/Douvres
    if 1.0 < lon < 2.5 and lat > 53:
        return True, "Calais_Aberrant_North"
    
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

def create_point_geometry(lat, lon, location_str=None):
    """Crée une géométrie Point au format WKT avec validation et géocodage de secours"""
    if pd.isna(lat) or pd.isna(lon):
        # Si pas de coordonnées, essayer le géocodage
        if location_str:
            print(f"  ℹ️  Coordonnées manquantes, tentative de géocodage: '{location_str}'")
            lat, lon = geocode_location(location_str)
            if lat is None or lon is None:
                return None, None, None
        else:
            return None, None, None
    
    # Vérifier si les coordonnées sont suspectes
    is_suspicious, reason = is_suspicious_coordinate(lat, lon)
    if is_suspicious:
        print(f"Coordonnée suspecte ignorée ({reason}): {lon}, {lat}")
        # Essayer le géocodage de secours
        if location_str:
            print(f"  🔄 Tentative de géocodage de secours: '{location_str}'")
            lat_new, lon_new = geocode_location(location_str)
            if lat_new is not None and lon_new is not None:
                # Vérifier que les nouvelles coordonnées sont valides
                is_suspicious_new, reason_new = is_suspicious_coordinate(lat_new, lon_new)
                if not is_suspicious_new:
                    lat, lon = lat_new, lon_new
                else:
                    print(f"  ✗ Géocodage invalide ({reason_new}): {lon_new}, {lat_new}")
                    return None, None, None
            else:
                return None, None, None
        else:
            return None, None, None
    
    try:
        return f"POINT({float(lon)} {float(lat)})", float(lat), float(lon)
    except:
        return None, None, None

def get_row_sources(row, max_sources=5):
    """Retourne la liste des sources non vides pour une ligne"""
    sources = []
    for i in range(1, max_sources + 1):
        col_name = f'source{i}'
        source_url = row.get(col_name)
        if pd.notna(source_url) and str(source_url).strip() != '':
            sources.append(str(source_url).strip())
    return sources

# ============================================================================
# ANALYSE POUR IDENTIFIER LES ÉVÉNEMENTS COLLECTIFS (DATE + SOURCE)
# ============================================================================

print("\n=== Identification des événements collectifs par date et source ===")

# Dictionnaire pour regrouper par source
source_date_groups = {}

df["latitude_corrigee"] = pd.NA
df["longitude_corrigee"] = pd.NA

for idx, row in df.iterrows():
    row_id = row['id']
    death_date = parse_calais_date(row.get('date'))
    if not death_date:
        continue

    row_sources = get_row_sources(row)
    if not row_sources:
        continue

    for source_url in row_sources:
        if source_url not in source_date_groups:
            source_date_groups[source_url] = []
        source_date_groups[source_url].append((death_date, row_id))

# Regrouper par source avec tolérance +/- 1 jour
candidate_groups = []
for source_url, items in source_date_groups.items():
    items.sort(key=lambda x: x[0])
    current_group = [items[0]]
    min_date = items[0][0]
    max_date = items[0][0]

    for date_value, row_id in items[1:]:
        new_min = min(min_date, date_value)
        new_max = max(max_date, date_value)
        if (new_max - new_min).days <= 1:
            current_group.append((date_value, row_id))
            min_date = new_min
            max_date = new_max
        else:
            if len(current_group) > 1:
                candidate_groups.append({rid for _, rid in current_group})
            current_group = [(date_value, row_id)]
            min_date = date_value
            max_date = date_value

    if len(current_group) > 1:
        candidate_groups.append({rid for _, rid in current_group})

# Dédupliquer les groupes identiques (peuvent apparaître via plusieurs sources)
unique_groups = {}
for group in candidate_groups:
    key = frozenset(group)
    if len(key) > 1:
        unique_groups[key] = group

shared_events = list(unique_groups.values())

print(f"Nombre total de sources uniques: {len(source_date_groups)}")
print(f"Nombre d'événements collectifs identifiés: {len(shared_events)}")

if len(shared_events) > 0:
    print("\nExemples d'événements collectifs:")
    for i, ids in enumerate(shared_events[:5]):
        print(f"  Groupe {i+1}: {len(ids)} personnes (IDs: {list(ids)[:5]})")

# ============================================================================
# CRÉATION DES PERSONNES ET DES ÉVÉNEMENTS DE MORT
# ============================================================================

print("\n=== Création des personnes et des événements de mort ===")

# Dictionnaire pour mapper les URLs de sources à des IDs numériques
source_url_to_id = {}
source_id_counter = 1

# Dictionnaire pour stocker les sources de chaque événement de mort
death_event_sources = {}

# Colonnes possibles pour repatriation (optionnelles)
repatriation_columns = [
    col for col in df.columns
    if col.lower() in ("repatriated", "repatriation", "rapatrie", "rapatriement")
]

# Compteurs pour les statistiques
age_from_exact_count = 0
age_from_minor_count = 0

for idx, row in df.iterrows():
    person_id = row['id']
    
    # Créer l'URI de la personne
    person_uri = FRONTLET_DATA[f"calais_person_{person_id}"]
    
    # Ajouter la personne au graphe
    g.add((person_uri, RDF.type, FRONTLET.Person))
    g.add((person_uri, RDFS.label, Literal(f"Person {person_id}", lang="en")))
    
    # Ajouter le nom si disponible
    if pd.notna(row.get('name')) and str(row['name']).strip() != '':
        person_name = str(row['name']).strip()
        g.add((person_uri, FRONTLET.hasName, Literal(person_name)))

    # Pays d'origine (nationalité)
    origin_country_node = None
    origin_country_val = None
    if pd.notna(row.get('nationalite')) and str(row.get('nationalite')).strip() != '':
        origin_country_val = row.get('nationalite')
    elif pd.notna(row.get('nationality')) and str(row.get('nationality')).strip() != '':
        origin_country_val = row.get('nationality')

    if origin_country_val is not None:
        origin_country_node = ensure_country_node(origin_country_val)
    
    # Ajouter l'âge si disponible
    age_value, is_precise = parse_age(row.get('age'))
    if age_value is not None:
        # La colonne age est remplie, on lui donne la priorité
        age_uri = FRONTLET_DATA[f"calais_age_{person_id}"]
        g.add((age_uri, RDF.type, FRONTLET.Age))
        g.add((age_uri, FRONTLET.hasAge, Literal(age_value, datatype=XSD.integer)))
        g.add((age_uri, FRONTLET.hasPrecision, Literal(is_precise, datatype=XSD.boolean)))
        g.add((person_uri, FRONTLET.aged, age_uri))
        age_from_exact_count += 1
    else:
        # Si age est vide, vérifier la colonne 'minor' pour créer un intervalle d'âge
        age_uri = create_age_interval_from_minor(row.get('minor (Y/N)'), person_id)
        if age_uri:
            g.add((person_uri, FRONTLET.aged, age_uri))
            age_from_minor_count += 1
    
    # Ajouter le genre si disponible
    gender_uri = find_gender_in_thesaurus(row.get('Genre (H/F)'))
    if gender_uri:
        g.add((person_uri, FRONTLET.hasGender, gender_uri))
    
    # Créer l'événement de mort
    death_event_uri = FRONTLET_DATA[f"calais_death_{person_id}"]
    g.add((death_event_uri, RDF.type, FRONTLET.Death))
    g.add((death_event_uri, RDF.type, FRONTLET.IndividualEvent))
    g.add((death_event_uri, RDFS.label, Literal(f"Death event {person_id}", lang="en")))
    
    # Lier la personne à l'événement de mort
    g.add((death_event_uri, FRONTLET.livedBy, person_uri))
    g.add((person_uri, FRONTLET.composedOf, death_event_uri))
    
    # Ajouter la date de mort
    death_date = parse_calais_date(row.get('date'))
    if death_date:
        date_str = death_date.strftime("%Y-%m-%d")
        g.add((death_event_uri, TIME.inXSDDate, Literal(date_str, datatype=XSD.date)))
    
    # Créer la géométrie (Point) avec latitude et longitude
    geometry_wkt, lat_corr, lon_corr = create_point_geometry(
        row.get('latitude'), row.get('longitude'), row.get('location')
    )

    if lat_corr is not None and lon_corr is not None:
        df.at[idx, "latitude_corrigee"] = lat_corr
        df.at[idx, "longitude_corrigee"] = lon_corr

    if geometry_wkt:
        geometry_uri = FRONTLET_DATA[f"calais_geometry_{person_id}"]
        g.add((geometry_uri, RDF.type, GEO.Geometry))
        g.add((geometry_uri, GEO.asWKT, Literal(geometry_wkt, datatype=GEO.wktLiteral)))
        g.add((death_event_uri, GEO.hasGeometry, geometry_uri))
    
    # Ajouter la cause de mort si disponible
    death_cause_uri = find_death_cause_in_thesaurus(row.get('cause'))
    if death_cause_uri:
        g.add((death_event_uri, FRONTLET.hasDeathCause, death_cause_uri))

    # Événement de rapatriement (si colonne présente)
    if repatriation_columns:
        rep_val = None
        for col in repatriation_columns:
            val = row.get(col)
            if pd.notna(val) and str(val).strip() != '':
                rep_val = val
                break

        if rep_val is not None:
            repatriation_event_uri = FRONTLET_DATA[f"calais_repatriation_{person_id}"]
            g.add((repatriation_event_uri, RDF.type, FRONTLET.Repatriation))
            g.add((repatriation_event_uri, RDF.type, FRONTLET.IndividualEvent))
            g.add((person_uri, FRONTLET.composedOf, repatriation_event_uri))
            if origin_country_node:
                g.add((repatriation_event_uri, FRONTLET.targetCountry, origin_country_node))
    
    # Collecter les sources de cette ligne
    row_sources = []
    for i in range(1, 6):
        col_name = f'source{i}'
        if col_name in df.columns:
            source_url = row.get(col_name)
            if pd.notna(source_url) and str(source_url).strip() != '':
                row_sources.append(str(source_url).strip())
    
    # Stocker les sources pour cet événement de mort
    death_event_sources[death_event_uri] = row_sources
    
    # Ajouter toutes les sources directement sur l'événement de mort
    for source_url in row_sources:
        # Obtenir ou créer un ID numérique pour cette source
        if source_url not in source_url_to_id:
            source_url_to_id[source_url] = source_id_counter
            source_id_counter += 1
        
        source_id = source_url_to_id[source_url]
        source_uri = FRONTLET_DATA[f"calais_source_{source_id}"]
        g.add((source_uri, RDF.type, FRONTLET.Source))
        g.add((source_uri, FRONTLET.hasWebLink, Literal(source_url)))
        g.add((death_event_uri, FRONTLET.sourcedBy, source_uri))

print(f"Nombre de personnes créées: {len(df)}")
print(f"Nombre d'événements de mort créés: {len(df)}")
print(f"\n--- Statistiques sur les objets Age ---")
print(f"Objets Age créés à partir de la colonne 'age': {age_from_exact_count}")
print(f"Objets Age créés à partir de la colonne 'minor (Y/N)': {age_from_minor_count}")
print(f"Total d'objets Age créés: {age_from_exact_count + age_from_minor_count}")

# ============================================================================
# CRÉATION DES ÉVÉNEMENTS COLLECTIFS (DATE + LOCATION)
# ============================================================================

print("\n=== Création des événements collectifs ===")

collective_event_counter = 1

for person_ids in shared_events:
    # Créer l'événement collectif
    collective_event_uri = FRONTLET_DATA[f"calais_collective_event_{collective_event_counter}"]
    g.add((collective_event_uri, RDF.type, FRONTLET.CollectiveEvent))
    g.add((collective_event_uri, RDFS.label, Literal(f"Collective event {collective_event_counter}", lang="en")))
    
    # Lier les événements de mort individuels à l'événement collectif
    for person_id in person_ids:
        death_event_uri = FRONTLET_DATA[f"calais_death_{person_id}"]
        g.add((death_event_uri, FRONTLET.group, collective_event_uri))
        g.add((collective_event_uri, FRONTLET.memberOf, death_event_uri))
        
        # Ajouter les sources de cet événement individuel sur l'événement collectif aussi
        if death_event_uri in death_event_sources:
            for source_url in death_event_sources[death_event_uri]:
                if source_url not in source_url_to_id:
                    source_url_to_id[source_url] = source_id_counter
                    source_id_counter += 1
                
                source_id = source_url_to_id[source_url]
                source_uri = FRONTLET_DATA[f"calais_source_{source_id}"]
                g.add((source_uri, RDF.type, FRONTLET.Source))
                g.add((source_uri, FRONTLET.hasWebLink, Literal(source_url)))
                g.add((collective_event_uri, FRONTLET.sourcedBy, source_uri))
    
    collective_event_counter += 1

print(f"Nombre d'événements collectifs créés: {collective_event_counter - 1}")

# ============================================================================
# EXPORT DU GRAPHE RDF
# ============================================================================

print("\n=== Export du graphe RDF ===")
print(f"Nombre total de triples: {len(g)}")

output_file = "c:/Users/bresra/Desktop/ontoSequenceEvenement/calais/calais_output.ttl"
g.serialize(destination=output_file, format='turtle')

print(f"Export terminé: {output_file}")
print("\n=== Traitement terminé avec succès ===")

# ============================================================================
# EXÉCUTION DU COMPARATEUR CALAIS/UNITED ET EXPORT EXCEL
# ============================================================================

print("\n=== Comparaison Calais/United et export Excel ===")
matches_df = build_calais_united_matches()

if "id" in df.columns and "id" in matches_df.columns:
    merge_key = "id"
else:
    merge_key = None

if merge_key:
    merged_df = df.merge(
        matches_df[[merge_key, "UNITED_RECORD_ID_NR", "MATCH_TYPE"]],
        on=merge_key,
        how="left",
    )
else:
    matches_subset = matches_df[["UNITED_RECORD_ID_NR", "MATCH_TYPE"]]
    merged_df = pd.concat([df.reset_index(drop=True), matches_subset.reset_index(drop=True)], axis=1)

excel_output = "c:/Users/bresra/Desktop/ontoSequenceEvenement/calais/calais_with_united_matches.xlsx"
merged_df.to_excel(excel_output, index=False)
print(f"Export Excel terminé: {excel_output}")
