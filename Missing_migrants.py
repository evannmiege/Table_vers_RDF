#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Importer Missing Migrants (CSV/XLSX) vers RDF frontlet.

Implemented rules:
- Source: Information Source, Article title, URL
- Geometry: Coordinates -> geo:asWKT, fallback geocoding from Location of death (max 10 calls)
- Country: Country of Origin
- DeathCause: Cause of Death
- IndividualEvent multiplicity from Total Number of Dead and Missing
- DeathInjury typing with Death and Injury subclasses using Number of Dead / Minimum Estimated Number of Missing
- CollectiveEvent when total dead+missing >= 2
- Date from Website Date (DD/MM/YYYY), fallback Reported Month + Incident year
"""

from rdflib import Graph, Namespace, URIRef, Literal
from rdflib.namespace import RDF, RDFS, SKOS, XSD
import pandas as pd
import unicodedata
import re
import os
import math
import pycountry
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
INPUT_CANDIDATES = [
    "Missing_migrants/Missing_migrants.csv",
    "Missing_migrants/Missing_migrants.xlsx",
]
OUTPUT_TTL = "Missing_migrants/frontlet_import_output.ttl"
MAPPING_PATH = "Missing_migrants/mappingMissingMigrantsThesaurusCauseMort.csv"


# Espaces de noms par defaut
F = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
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
    return s_norm in ("nan", "none", "n/a", "na", "-", "null")


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


def parse_int_value(value):
    if is_missing(value):
        return None
    text = str(value).strip()
    text = re.sub(r"[^0-9\-]", "", text)
    if text in ("", "-"):
        return None
    try:
        return int(text)
    except Exception:
        return None


def month_to_number(month_name):
    if is_missing(month_name):
        return None
    mapping = {
        "january": "01",
        "february": "02",
        "march": "03",
        "april": "04",
        "may": "05",
        "june": "06",
        "july": "07",
        "august": "08",
        "september": "09",
        "october": "10",
        "november": "11",
        "december": "12",
    }
    return mapping.get(norm(month_name))


def build_event_date(website_date, reported_month, incident_year):
    """
    Return a date string:
    - DD/MM/YYYY from Website Date if valid
    - MM/YYYY from Reported Month + Incident year
    - YYYY from Incident year only
    - None when year is missing
    Also returns True when Website Date was present but invalid format.
    """
    website_invalid = False

    if not is_missing(website_date):
        date_text = str(website_date).strip()
        if re.fullmatch(r"\d{2}/\d{2}/\d{4}", date_text):
            return date_text, website_invalid
        website_invalid = True

    year_text = None
    if not is_missing(incident_year):
        m = re.search(r"\d{4}", str(incident_year))
        if m:
            year_text = m.group(0)

    if year_text is None:
        return None, website_invalid

    month_num = month_to_number(reported_month)
    if month_num is not None:
        return f"{month_num}/{year_text}", website_invalid

    return year_text, website_invalid


def parse_coordinate_pair(value):
    """
    Parse coordinates from forms like:
    - "lat, lon"
    - "lat lon"
    - "POINT(lon lat)"
    Returns (lat, lon) or (None, None).
    """
    if is_missing(value):
        return None, None

    raw = str(value).strip()
    point_match = re.search(
        r"POINT\s*\(\s*(-?\d+(?:[\.,]\d+)?)\s+(-?\d+(?:[\.,]\d+)?)\s*\)",
        raw,
        flags=re.IGNORECASE,
    )
    if point_match:
        lon = float(point_match.group(1).replace(",", "."))
        lat = float(point_match.group(2).replace(",", "."))
        return lat, lon

    nums = re.findall(r"-?\d+(?:[\.,]\d+)?", raw)
    if len(nums) >= 2:
        a = float(nums[0].replace(",", "."))
        b = float(nums[1].replace(",", "."))
        if abs(a) <= 90 and abs(b) <= 180:
            return a, b
        if abs(a) <= 180 and abs(b) <= 90:
            return b, a

    return None, None


def extract_coordinates_from_text(location_text):
    if is_missing(location_text):
        return None, None

    text = str(location_text).strip()
    patterns = [
        r"(?P<lat>\d+(?:[.,]\d+)?)\s*°?\s*(?P<lat_dir>[NS])[\s,;]+(?P<lon>\d+(?:[.,]\d+)?)\s*°?\s*(?P<lon_dir>[EW])",
        r"(?P<lat_dir>[NS])\s*(?P<lat>\d+(?:[.,]\d+)?)\s*°?[\s,;]+(?P<lon_dir>[EW])\s*(?P<lon>\d+(?:[.,]\d+)?)",
        r"(?P<lon>\d+(?:[.,]\d+)?)\s*°?\s*(?P<lon_dir>[EW])[\s,;]+(?P<lat>\d+(?:[.,]\d+)?)\s*°?\s*(?P<lat_dir>[NS])",
    ]

    for pattern in patterns:
        match = re.search(pattern, text, flags=re.IGNORECASE)
        if not match:
            continue
        try:
            lat = float(match.group("lat").replace(",", "."))
            lon = float(match.group("lon").replace(",", "."))
            if match.group("lat_dir").upper() == "S":
                lat = -lat
            if match.group("lon_dir").upper() == "W":
                lon = -lon
            return lat, lon
        except Exception:
            continue

    return None, None


def clean_location_for_geocoding(location_text):
    if is_missing(location_text):
        return ""
    cleaned = str(location_text).strip()
    cleaned = re.sub(r"\s+", " ", cleaned).strip(" ,;.-")
    return cleaned


def is_suspicious_coordinate(lat, lon):
    try:
        lat = float(lat)
        lon = float(lon)
    except Exception:
        return True, "PARSE_ERROR"

    if lon == -99 and lat == -99:
        return True, "ERROR_-99,-99"
    if abs(lon) > 180 or abs(lat) > 90:
        return True, "OUT_OF_BOUNDS"
    return False, "OK"


def ensure_country_node(g, country_code_or_name):
    if is_missing(country_code_or_name):
        return None

    val = str(country_code_or_name).strip()
    cc = None
    sval = re.sub(r"[^A-Za-z0-9]", "", val).upper()
    try:
        if re.fullmatch(r"[A-Z]{2}", sval):
            cc = pycountry.countries.get(alpha_2=sval)
        elif re.fullmatch(r"[A-Z]{3}", sval):
            cc = pycountry.countries.get(alpha_3=sval)
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
        uri = DATA["missing_Country_" + iso3.upper()]
        if (uri, None, None) not in g:
            g.add((uri, RDF.type, F.Country))
            g.add((uri, RDFS.label, Literal(getattr(cc, "name", val), lang="en")))
            g.add((uri, F.isoAlpha2, Literal(getattr(cc, "alpha_2", ""))))
            g.add((uri, F.isoAlpha3, Literal(getattr(cc, "alpha_3", ""))))
            g.add((uri, SKOS.notation, Literal(getattr(cc, "alpha_3", ""))))
        return uri

    candidate = find_by_label(g, country_code_or_name)
    if candidate:
        return candidate

    slug = re.sub(r"[^a-z0-9_]", "_", norm(country_code_or_name)).strip("_")
    if slug in ("", "nan", "none", "n_a"):
        return None

    uri = DATA["missing_Country_" + slug]
    if (uri, None, None) not in g:
        g.add((uri, RDF.type, F.Country))
        g.add((uri, RDFS.label, Literal(str(country_code_or_name).strip())))
    return uri


def find_thesaurus_term_by_prefLabel_fr(g, label_fr):
    if label_fr is None or str(label_fr).strip() == "":
        return None
    for s, _, o in g.triples((None, SKOS.prefLabel, None)):
        if norm(o) == norm(label_fr):
            return s
    for s, _, o in g.triples((None, RDFS.label, None)):
        if norm(o) == norm(label_fr):
            return s
    return None


def load_death_cause_thesaurus(g):
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
    mapping = {}
    mapping_nature = {}
    if not os.path.exists(mapping_path):
        print(f"Info: No mapping file found at {mapping_path}, direct matching only")
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
            return mapping
        cols = list(mdf.columns)
        if len(cols) >= 2:
            source_col = cols[0]
            thes_col = cols[1]
            nature_col = cols[2] if len(cols) >= 3 and "nature" in str(cols[2]).lower() else None
            for _, r in mdf.iterrows():
                src = norm(r.get(source_col, ""))
                tgt = norm(r.get(thes_col, ""))
                if src and tgt:
                    mapping[src] = tgt
                if nature_col:
                    nat = str(r.get(nature_col, "")).strip()
                    if src and nat and nat.lower() not in ("", "nan", "none"):
                        mapping_nature[src] = nat
            print(f"Loaded {len(mapping)} Cause-of-Death mappings from CSV")
    except Exception as e:
        print(f"Warning: Could not load mapping CSV {mapping_path}: {e}")
    return mapping, mapping_nature


def match_death_cause(value, mapping_dict, thesaurus_map):
    if not value or is_missing(value):
        return None, None

    val_norm = norm(value)
    mapped_label = mapping_dict.get(val_norm)
    if mapped_label and mapped_label in thesaurus_map:
        return thesaurus_map[mapped_label], mapped_label

    if val_norm in thesaurus_map:
        return thesaurus_map[val_norm], val_norm

    for lbl, uri in thesaurus_map.items():
        if lbl and lbl in val_norm:
            return uri, lbl

    return None, str(value).strip()


def resolve_input_path():
    for candidate in INPUT_CANDIDATES:
        if os.path.exists(candidate):
            return candidate
    raise FileNotFoundError(
        "No Missing Migrants input file found. Expected one of: "
        + ", ".join(INPUT_CANDIDATES)
    )


def read_input_table(path):
    if path.lower().endswith(".xlsx"):
        return pd.read_excel(path, dtype=str)

    encodings_to_try = ["utf-8-sig", "utf-8", "cp1252", "latin-1"]
    for enc in encodings_to_try:
        try:
            return pd.read_csv(
                path,
                sep=None,
                engine="python",
                dtype=str,
                keep_default_na=False,
                na_values=["", "NaN", "nan"],
                encoding=enc,
            )
        except UnicodeDecodeError:
            continue
    raise RuntimeError(f"Unable to read input table: {path}")


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

copy_all_class_hierarchy(g_ref, g)

thesaurus_map = load_death_cause_thesaurus(g_ref)
mapping_dict, mapping_nature = load_mapping_csv(MAPPING_PATH)

input_path = resolve_input_path()
df = read_input_table(input_path)
print(f"Input table: {input_path}")
print(f"Rows to process: {len(df)}")


# ---------------------- Preparation ----------------------
PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
INDIVIDUAL_EVENT_CLASS = find_by_label(g_ref, "Individual Event") or F.IndividualEvent
COLLECTIVE_EVENT_CLASS = find_by_label(g_ref, "Collective event") or F.CollectiveEvent
DEATH_INJURY_CLASS = find_by_label(g_ref, "Death injury") or F.DeathInjury
DEATH_CLASS = find_by_label(g_ref, "Death") or F.Death
INJURY_CLASS = find_by_label(g_ref, "Injury") or F.Injury
MISSING_CLASS = F.Missing

if (MISSING_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_CLASS, RDFS.subClassOf, F.IndividualEvent))
    g.add((MISSING_CLASS, RDFS.label, Literal("Missing", lang="en")))

PROP_composedOf = find_by_label(g_ref, "composedOf") or F.composedOf
PROP_birthPlace = find_by_label(g_ref, "birth place") or F.birthPlace
PROP_group = find_by_label(g_ref, "group") or F.group
PROP_hasDeathCause = find_by_label(g_ref, "has death cause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_gender = find_by_label(g_ref, "has gender") or F.hasGender
PROP_sourcedBy = find_by_label(g_ref, "sourced by") or F.sourcedBy
PROP_hasWebLink = find_by_label(g_ref, "url") or find_by_label(g_ref, "has web link") or F.hasWebLink
PROP_sourceInformation = find_by_label(g_ref, "information source") or find_by_label(g_ref, "has name") or F.hasName
PROP_sourceArticleTitle = find_by_label(g_ref, "article title") or find_by_label(g_ref, "has comment") or F.hasComment
PROP_totalDeadAndMissing = find_by_label(g_ref, "total dead and missing") or F.totalDeadAndMissing
PROP_numberDead = find_by_label(g_ref, "number dead") or F.numberDead
PROP_numberMissing = find_by_label(g_ref, "number of missing") or F.numberMissing
PROP_numberOfSurvivors = find_by_label(g_ref, "number of survivors") or F.numberOfSurvivors
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after

ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label)
THES_male = T.male
THES_female = T.female
THES_human = T.human


# --------------- Configuration du geocodage --------------
geolocator = Nominatim(user_agent="frontlet_missing_migrants_geocoder")
geocoding_cache = {}
MAX_DEATH_LOCATION_GEOCODING_CALLS = 10
death_location_geocoding_calls = 0
death_location_geocoding_success = 0


def geocode_location(location_name, max_retries=3):
    global death_location_geocoding_calls
    if is_missing(location_name):
        return None, None

    if death_location_geocoding_calls >= MAX_DEATH_LOCATION_GEOCODING_CALLS:
        return None, None
    death_location_geocoding_calls += 1

    location_str = clean_location_for_geocoding(location_name)
    if not location_str:
        return None, None

    cache_key = location_str.lower()
    if cache_key in geocoding_cache:
        return geocoding_cache[cache_key]

    for attempt in range(max_retries):
        try:
            time.sleep(1.1)
            location = geolocator.geocode(location_str, timeout=10)
            if location:
                coords = (location.latitude, location.longitude)
                geocoding_cache[cache_key] = coords
                return coords
            geocoding_cache[cache_key] = (None, None)
            return None, None
        except GeocoderTimedOut:
            if attempt < max_retries - 1:
                continue
            print(f"Geocoding timeout for: {location_name}")
        except GeocoderServiceError as e:
            print(f"Geocoding service error for {location_name}: {e}")
            break
        except Exception as e:
            print(f"Unexpected geocoding error for {location_name}: {e}")
            break

    geocoding_cache[cache_key] = (None, None)
    return None, None


# ------------------- Traitement des lignes ----------------
count_person = 0
count_individual_events = 0
count_collective_events = 0
count_sources = 0
count_cause_matched = 0
count_cause_literal = 0
count_nature_mapped = 0
count_website_date_invalid = 0
count_additional_typed_events = 0

for idx, row in df.iterrows():
    row_num = idx + 1

    person_uri = DATA[f"missing_Person_{row_num}"]
    g.add((person_uri, RDF.type, PERSON_CLASS))
    count_person += 1

    n_female = parse_int_value(row.get("Number of Females", "")) or 0
    n_male = parse_int_value(row.get("Number of Males", "")) or 0
    if n_female > 0 and n_male == 0:
        g.add((person_uri, PROP_gender, THES_female))
    elif n_male > 0 and n_female == 0:
        g.add((person_uri, PROP_gender, THES_male))

    # Country of Origin -> frontlet:Country
    country_origin = row.get("Country of Origin", "")
    birth_country = ensure_country_node(g, country_origin)
    if birth_country is not None:
        g.add((person_uri, PROP_birthPlace, birth_country))
        if not is_missing(country_origin):
            g.add((birth_country, RDFS.label, Literal(str(country_origin).strip())))

    # Multiplicite derivee de Total Number of Dead and Missing
    total_dead_missing = parse_int_value(row.get("Total Number of Dead and Missing", ""))
    if total_dead_missing is None or total_dead_missing < 1:
        total_dead_missing = 1

    number_dead = parse_int_value(row.get("Number of Dead", ""))
    number_missing = parse_int_value(row.get("Minimum Estimated Number of Missing", ""))
    number_survivors = parse_int_value(row.get("Number of Survivors", ""))

    number_dead = max(0, number_dead or 0)
    number_missing = max(0, number_missing or 0)
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Cause of Death", "Location of death", "Country of Origin"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Information Source", "Article title", "URL"], is_missing))

    collective_event_uri = None
    if total_dead_missing >= 2:
        incident_id = row.get("Incident ID", "")
        if is_missing(incident_id):
            incident_id = f"row_{row_num}"
        incident_slug = re.sub(r"[^A-Za-z0-9_-]", "_", str(incident_id).strip())
        collective_event_uri = DATA[f"missing_CollectiveEvent_{incident_slug}"]

        if (collective_event_uri, None, None) not in g:
            g.add((collective_event_uri, RDF.type, COLLECTIVE_EVENT_CLASS))
            g.add((collective_event_uri, RDFS.label, Literal(str(incident_id).strip())))
            g.add((collective_event_uri, PROP_totalDeadAndMissing, Literal(total_dead_missing, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_numberDead, Literal(number_dead, datatype=XSD.integer)))
            g.add((collective_event_uri, PROP_numberMissing, Literal(number_missing, datatype=XSD.integer)))
            if number_survivors is not None:
                g.add((collective_event_uri, PROP_numberOfSurvivors, Literal(number_survivors, datatype=XSD.integer)))
            count_collective_events += 1

    event_uris = []
    death_idx = 0
    missing_idx = 0
    for event_pos in range(total_dead_missing):
        # Garder des familles d'URI separees pour distinguer clairement Death et Missing a l'export.
        if event_pos < number_dead:
            death_idx += 1
            if number_dead == 1:
                event_uri = DATA[f"missing_Death_{row_num}"]
            else:
                event_uri = DATA[f"missing_Death_{row_num}_{death_idx}"]
        else:
            missing_idx += 1
            if number_missing == 1:
                event_uri = DATA[f"missing_MissingEvent_{row_num}"]
            else:
                event_uri = DATA[f"missing_MissingEvent_{row_num}_{missing_idx}"]

        g.add((event_uri, RDF.type, INDIVIDUAL_EVENT_CLASS))
        g.add((event_uri, RDF.type, DEATH_INJURY_CLASS))

        # Repartition Death/Injury
        if event_pos < number_dead:
            g.add((event_uri, RDF.type, DEATH_CLASS))
        elif event_pos < number_dead + number_missing:
            g.add((event_uri, RDF.type, MISSING_CLASS))

        g.add((person_uri, PROP_composedOf, event_uri))
        if collective_event_uri is not None:
            g.add((event_uri, PROP_group, collective_event_uri))

        event_uris.append(event_uri)
        count_individual_events += 1

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, ev_uri) for ev_uri in event_uris],
        collective_event_uri,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "missing",
        row_num,
        F,
        RDF,
        Literal,
        PROP_composedOf,
        PROP_group,
        PROP_temporal_before,
        PROP_temporal_after,
        PROP_sourceArticleTitle,
        PROP_sourceArticleTitle,
    )
    count_additional_typed_events += sum(additional_counts.values())

    # Date logic
    event_date, website_invalid = build_event_date(
        row.get("Website Date", ""),
        row.get("Reported Month", ""),
        row.get("Incident year", ""),
    )
    if website_invalid:
        count_website_date_invalid += 1
    if event_date is not None:
        weekday_name = infer_day_of_week_name(event_date)
        for ev_uri in event_uris:
            g.add((ev_uri, TIME.inXSDDate, Literal(event_date)))
            if weekday_name:
                g.add((ev_uri, TIME.dayOfWeek, TIME[weekday_name]))
                g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
                g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))

    # Cause of Death -> thesaurus DeathCause
    cause_val = row.get("Cause of Death", "")
    if not is_missing(cause_val):
        cause_uri, cause_lbl = match_death_cause(cause_val, mapping_dict, thesaurus_map)
        if cause_uri is not None:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, cause_uri))
            count_cause_matched += 1
        elif cause_lbl:
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathCause, Literal(cause_lbl)))
            count_cause_literal += 1

        nature_label = mapping_nature.get(norm(cause_val))
        if nature_label:
            nature_slug = re.sub(r"[^a-z0-9_]", "_", norm(nature_label)).strip("_") or "unknown"
            nature_uri = DATA[f"missing_DeathNature_{nature_slug}"]
            if (nature_uri, RDF.type, F.DeathNature) not in g:
                g.add((nature_uri, RDF.type, F.DeathNature))
                g.add((nature_uri, RDFS.label, Literal(str(nature_label).strip())))
            for ev_uri in event_uris:
                g.add((ev_uri, PROP_hasDeathNature, nature_uri))
            count_nature_mapped += 1

        cause_text = norm(cause_val)
        route_text = norm(row.get("Migration route", ""))
        transport_mode = None
        if any(k in cause_text for k in ("drown", "drowning", "boat", "ship", "vessel", "ferry", "raft", "sea")):
            transport_mode = T.boat if hasattr(T, "boat") else None
        elif any(k in (cause_text + " " + route_text) for k in ("truck", "lorry", "vehicle", "car", "van", "bus", "train", "rail")):
            transport_mode = T.landVehicle if hasattr(T, "landVehicle") else THES_human
        elif any(k in route_text for k in ("land", "overland", "on foot", "foot", "desert", "walk")):
            transport_mode = THES_human
        if transport_mode is not None:
            for ev_uri in event_uris:
                g.add((ev_uri, F.transportMode, transport_mode))

    # Geometrie: coordonnees en priorite, geocoder Location of death si absent
    lat_f, lon_f = parse_coordinate_pair(row.get("Coordinates", ""))
    if lat_f is None or lon_f is None:
        lat_f, lon_f = extract_coordinates_from_text(row.get("Coordinates", ""))

    location_of_death = row.get("Location of death", "")
    if (lat_f is None or lon_f is None) and not is_missing(location_of_death):
        if death_location_geocoding_calls < MAX_DEATH_LOCATION_GEOCODING_CALLS:
            death_location_geocoding_calls += 1
            lat_geo, lon_geo = geocode_location(location_of_death)
            if lat_geo is not None and lon_geo is not None:
                lat_f, lon_f = lat_geo, lon_geo
                death_location_geocoding_success += 1

    if lat_f is not None and lon_f is not None and math.isfinite(lat_f) and math.isfinite(lon_f):
        suspicious, reason = is_suspicious_coordinate(lat_f, lon_f)
        if not suspicious:
            wkt = f"POINT({lon_f} {lat_f})"
            for ev_pos, ev_uri in enumerate(event_uris, start=1):
                geometry_uri = DATA[f"missing_geometry_{row_num}_{ev_pos}"]
                g.add((ev_uri, GEO.hasGeometry, geometry_uri))
                g.add((geometry_uri, RDF.type, GEO.Geometry))
                g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
        else:
            print(f"Warning: suspicious coordinate ignored ({reason}) at row {row_num}: {lon_f}, {lat_f}")

    # Source: Information Source, titre de l'article, URL
    information_source = row.get("Information Source", "")
    article_title = row.get("Article title", "")
    url = row.get("URL", "")

    has_source_payload = any(not is_missing(v) for v in (information_source, article_title, url))
    if has_source_payload:
        source_uri = DATA[f"missing_Source_{row_num}"]
        g.add((source_uri, RDF.type, F.Source))
        _combined_mm_source = " ".join(filter(None, [str(information_source).strip() if not is_missing(information_source) else "", str(article_title).strip() if not is_missing(article_title) else ""]))
        _mm_source_category = infer_source_category_key(_combined_mm_source)
        _MM_SOURCE_SUBTYPE_MAP = {"family": F.Family, "media": F.Media, "civil_society": F.CivilSociety, "death_certificate": F.DeathCertificate, "official_document": F.OtherOfficialDocument}
        _mm_sub_type = _MM_SOURCE_SUBTYPE_MAP.get(_mm_source_category)
        if _mm_sub_type:
            g.add((source_uri, RDF.type, _mm_sub_type))

        if not is_missing(information_source):
            source_txt = str(information_source).strip()
            g.add((source_uri, PROP_sourceInformation, Literal(source_txt)))
            g.add((source_uri, RDFS.label, Literal(source_txt)))

        if not is_missing(article_title):
            g.add((source_uri, PROP_sourceArticleTitle, Literal(str(article_title).strip())))

        if not is_missing(url):
            g.add((source_uri, PROP_hasWebLink, Literal(str(url).strip())))

        for ev_uri in event_uris:
            g.add((ev_uri, PROP_sourcedBy, source_uri))
        count_sources += 1


# --------------------- Resume et sortie ------------------
g.serialize(destination=OUTPUT_TTL, format="turtle")

print("\n" + "=" * 60)
print("Import Missing Migrants complete.")
print("=" * 60)
print(f"Rows processed (persons): {count_person}")
print(f"Individual events created: {count_individual_events}")
print(f"Collective events created: {count_collective_events}")
print(f"Sources created: {count_sources}")
print(f"Cause matched to thesaurus URI: {count_cause_matched}")
print(f"Cause fallback literal: {count_cause_literal}")
print(f"DeathNature linked: {count_nature_mapped}")
print(f"Other typed events created: {count_additional_typed_events}")
print(f"Website Date invalid format count: {count_website_date_invalid}")
print(
    f"Location-of-death geocoding calls: "
    f"{death_location_geocoding_calls}/{MAX_DEATH_LOCATION_GEOCODING_CALLS}"
)
print(f"Location-of-death geocoding successes: {death_location_geocoding_success}")
print("=" * 60)
print(f"Output written to: {OUTPUT_TTL}")

