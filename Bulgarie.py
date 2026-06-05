#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from datetime import datetime
import re
import time
import unicodedata
from urllib.parse import unquote

import pandas as pd
import pycountry
from geopy.exc import GeocoderRateLimited, GeocoderServiceError, GeocoderTimedOut
from geopy.geocoders import Photon
from rdflib import Graph, Literal, Namespace, URIRef
from rdflib.namespace import RDF, RDFS, SKOS, XSD
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


ONTO_PATH = "frontletOnto.ttl"
THES_PATH = "frontletThesaurus.ttl"
SOURCE_PATH = "Bulgarie/Bulgarie.xlsx"
MAPPING_PATH = "Bulgarie/mappingBulgarieThesaurusCauseMort.csv"
OUTPUT_TTL = "Bulgarie/frontlet_import_output.ttl"
ROW_LIMIT = None

F = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T = Namespace("http://data/frontlet/thesaurus#")
GEO = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")

LOCATION_COORDINATE_OVERRIDES = {
    "vojnegovac": (43.0756042, 22.6351640),
    "village of vojnegovac": (43.0756042, 22.6351640),
}

INHUMATION_BURIAL_MARKERS = (
    "buried",
    "burial",
    "cemetery",
    "cemetary",
    "grave",
    "graveyard",
    "interment",
    "inhum",
    "cimetiere",
    "cimeti",
)

INHUMATION_NO_GEO_MARKERS = (
    "morgue",
    "hospital",
    "family doesn't know",
    "family doesnt know",
    "unclear",
    "unknown",
    "not known",
)

GEOCODER_MIN_DELAY_SECONDS = 2.0
GEOCODER_MAX_ATTEMPTS = 4
GEOCODER_RATE_LIMIT_BACKOFF_SECONDS = 10.0
GEOCODER_COUNTRY_HINT = "Bulgaria"


def norm(value):
    if value is None:
        return ""
    text = str(value).strip()
    text = unicodedata.normalize("NFKD", text)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = re.sub(r"\s+", " ", text)
    return text.lower()


def is_missing(value):
    if value is None:
        return True
    text = norm(value)
    return text in {
        "",
        "nan",
        "none",
        "null",
        "n/a",
        "na",
        "unknown",
        "unclear",
        "family doesn't know",
        "family doesnt know",
        "not known",
        "-",
    }


def slugify(value):
    cleaned = re.sub(r"[^a-z0-9_]+", "_", norm(value))
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    return cleaned or "unknown"


def find_by_label(graph, search, props=(RDFS.label, SKOS.prefLabel)):
    if is_missing(search):
        return None
    search_norm = norm(search)
    for predicate in props:
        for subject, _, obj in graph.triples((None, predicate, None)):
            if norm(obj) == search_norm:
                return subject
    for predicate in props:
        for subject, _, obj in graph.triples((None, predicate, None)):
            if search_norm in norm(obj):
                return subject
    return None


def copy_all_class_hierarchy(graph_src, graph_dst):
    predicates = (RDF.type, RDFS.subClassOf, SKOS.prefLabel, SKOS.definition, RDFS.label)
    class_uris = {
        subject
        for subject in graph_src.subjects(RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class"))
        if str(subject).startswith(str(F))
    }
    expanded = set(class_uris)
    for class_uri in list(class_uris):
        for child, _, _ in graph_src.triples((None, RDFS.subClassOf, class_uri)):
            if str(child).startswith(str(F)):
                expanded.add(child)

    for class_uri in expanded:
        for predicate in predicates:
            for _, _, obj in graph_src.triples((class_uri, predicate, None)):
                graph_dst.add((class_uri, predicate, obj))


def copy_resource_description(graph_src, graph_dst, resource_uri, predicates=None):
    if resource_uri is None:
        return
    predicates = predicates or (RDF.type, RDFS.label, RDFS.comment, SKOS.prefLabel, SKOS.broader)
    for predicate in predicates:
        for _, _, obj in graph_src.triples((resource_uri, predicate, None)):
            graph_dst.add((resource_uri, predicate, obj))


def load_source_dataframe(path):
    last_error = None
    for kwargs in ({}, {"engine": "openpyxl"}):
        try:
            return pd.read_excel(path, dtype=str, **kwargs)
        except Exception as exc:
            last_error = exc
    raise RuntimeError(f"cannot read source workbook: {path}") from last_error


def load_mapping_csv(path):
    mapping_df = pd.read_csv(path, sep=";", dtype=str).fillna("")
    mapping_dict = {}
    mapping_nature = {}
    for _, row in mapping_df.iterrows():
        source_value = row.get("Bulgarie", "")
        key = norm(source_value)
        if not key:
            continue
        mapping_dict[key] = str(row.get("Thesaurus", "")).strip()
        nature_value = str(row.get("Nature", "")).strip()
        if nature_value:
            mapping_nature[key] = nature_value
    return mapping_dict, mapping_nature


def load_death_cause_thesaurus(graph):
    thesaurus_map = {}
    for subject, _, obj in graph.triples((None, SKOS.prefLabel, None)):
        if str(subject).startswith(str(T)):
            thesaurus_map[norm(obj)] = subject
    for subject, _, obj in graph.triples((None, RDFS.label, None)):
        if str(subject).startswith(str(T)):
            thesaurus_map.setdefault(norm(obj), subject)
    return thesaurus_map


def create_or_get_death_cause_instance(graph, cause_label, thesaurus_uri=None):
    if is_missing(cause_label):
        return None
    cause_uri = DATA[f"bulgarie_DeathCause_{slugify(cause_label)}"]
    if (cause_uri, RDF.type, F.DeathCause) not in graph:
        graph.add((cause_uri, RDF.type, F.DeathCause))
        graph.add((cause_uri, RDFS.label, Literal(str(cause_label).strip(), lang="fr")))
    if thesaurus_uri is not None:
        graph.add((cause_uri, SKOS.closeMatch, thesaurus_uri))
    return cause_uri


def create_or_get_death_nature_instance(graph, nature_label, thesaurus_uri=None):
    if is_missing(nature_label):
        return None
    nature_uri = DATA[f"bulgarie_DeathNature_{slugify(nature_label)}"]
    if (nature_uri, RDF.type, F.DeathNature) not in graph:
        graph.add((nature_uri, RDF.type, F.DeathNature))
        graph.add((nature_uri, RDFS.label, Literal(str(nature_label).strip(), lang="fr")))
    if thesaurus_uri is not None:
        graph.add((nature_uri, SKOS.closeMatch, thesaurus_uri))
    return nature_uri


def ensure_gender_instances(graph):
    specs = {
        "masculin": {"uri": DATA["bulgarie_Gender_masculin"], "label": "masculin", "match": T.male},
        "feminin": {"uri": DATA["bulgarie_Gender_feminin"], "label": "feminin", "match": T.female},
        "inconnu": {"uri": DATA["bulgarie_Gender_inconnu"], "label": "inconnu", "match": T.gender_unknown},
        "autre": {"uri": DATA["bulgarie_Gender_autre"], "label": "autre", "match": T.gender_other},
    }
    for spec in specs.values():
        if (spec["uri"], RDF.type, F.Gender) not in graph:
            graph.add((spec["uri"], RDF.type, F.Gender))
            graph.add((spec["uri"], RDFS.label, Literal(spec["label"], lang="fr")))
            graph.add((spec["uri"], SKOS.closeMatch, spec["match"]))
    return {"unknown": specs["inconnu"]["uri"]}


def get_value(row, names):
    for name in names:
        if name in row.index:
            value = row.get(name, "")
            if not is_missing(value):
                return str(value).strip()
    return ""


def get_raw_value(row, names):
    for name in names:
        if name in row.index:
            value = row.get(name, "")
            if value is None:
                continue
            text = str(value).strip()
            if text and text.lower() not in {"nan", "none", "null"}:
                return text
    return ""


def parse_birth_value(value):
    if is_missing(value):
        return None, None
    text = str(value).strip()
    if re.fullmatch(r"\d{4}", text):
        return Literal(int(text), datatype=XSD.integer), None
    for fmt in ("%d.%m.%Y", "%d.%m.%y", "%d/%m/%Y", "%Y-%m-%d", "%Y-%m-%d %H:%M:%S"):
        try:
            parsed = datetime.strptime(text, fmt)
            return Literal(parsed.year, datatype=XSD.integer), parsed.date().isoformat()
        except ValueError:
            continue
    match = re.search(r"(19|20)\d{2}", text)
    if match:
        return Literal(int(match.group(0)), datatype=XSD.integer), text
    return None, text


def parse_date_to_iso(value):
    if is_missing(value):
        return None, None
    text = str(value).strip()

    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d", "%d.%m.%Y", "%d.%m.%y", "%d/%m/%Y"):
        try:
            parsed = datetime.strptime(text, fmt)
            return parsed.date().isoformat(), None
        except ValueError:
            continue

    range_match = re.fullmatch(r"(\d{1,2})\s*/\s*(\d{1,2})\s+([A-Za-z]+)\s+(\d{4})", text)
    if range_match:
        day_start = int(range_match.group(1))
        month_name = range_match.group(3)
        year = int(range_match.group(4))
        try:
            parsed = datetime.strptime(f"{day_start} {month_name} {year}", "%d %B %Y")
            return parsed.date().isoformat(), text
        except ValueError:
            return None, text

    embedded_match = re.search(r"(19|20)\d{2}-\d{2}-\d{2}", text)
    if embedded_match:
        iso_text = embedded_match.group(0)
        return iso_text, text if iso_text != text else None

    return None, text


def match_death_cause(raw_value, mapping_dict, thesaurus_map, mapping_nature):
    if is_missing(raw_value):
        return None, None, None, False
    raw_text = str(raw_value).strip()
    raw_key = norm(raw_text)
    mapped_label = mapping_dict.get(raw_key)
    cause_nature = mapping_nature.get(raw_key)
    if mapped_label:
        return thesaurus_map.get(norm(mapped_label)), mapped_label, cause_nature, False
    return None, raw_text, None, True


def details_indicate_inhumation(*values):
    return any(str(value).strip() for value in values if value is not None)


def detect_transport_from_text(*values):
    text = " ".join(norm(v) for v in values if not is_missing(v))
    if not text:
        return None
    patterns = [
        ("train", ["train", "rail", "locomotive"]),
        ("car", ["car", "vehicle", "auto", "automobile"]),
        ("truck", ["truck", "lorry", "camion"]),
        ("bus", ["bus", "coach", "autobus"]),
        ("motorbike", ["motorbike", "motorcycle", "moto", "scooter"]),
        ("bicycle", ["bicycle", "bike", "cyclist"]),
        ("boat", ["boat", "ship", "vessel", "ferry", "raft", "dinghy", "drown", "drowning", "sea", "river"]),
        ("plane", ["plane", "aircraft", "airplane", "helicopter"]),
    ]
    for token, keywords in patterns:
        if any(k in text for k in keywords):
            return token
    return None


def parse_coordinates_from_text(value):
    if is_missing(value):
        return None, None
    text = str(value)

    # Décoder les URL-encodées (ex: %C2%B0 → °, %22 → ")
    text_decoded = unquote(text)

    for candidate_text in (text, text_decoded):
        # Décimal simple : lat, lon
        for pattern in (
            r"([-+]?\d{1,2}\.\d+)\s*,\s*([-+]?\d{1,3}\.\d+)",
            r"q=([-+]?\d{1,2}\.\d+),([-+]?\d{1,3}\.\d+)",
            # Google Maps @lat,lon,zoom
            r"@([-+]?\d{1,2}\.\d+),([-+]?\d{1,3}\.\d+)",
            # Google Maps data=...3d<lat>...4d<lon>
            r"3d([-+]?\d{1,2}\.\d+)[^0-9]*4d([-+]?\d{1,3}\.\d+)",
        ):
            match = re.search(pattern, candidate_text)
            if match:
                lat = float(match.group(1))
                lon = float(match.group(2))
                if -90 <= lat <= 90 and -180 <= lon <= 180:
                    return lat, lon

        dms_match = re.search(
            r"(\d{1,2})[°\s°]+(\d{1,2})['\s']+(\d{1,2}(?:\.\d+)?)[\"″\s]*([NS]).*?"
            r"(\d{1,3})[°\s°]+(\d{1,2})['\s']+(\d{1,2}(?:\.\d+)?)[\"″\s]*([EW])",
            candidate_text,
            flags=re.IGNORECASE,
        )
        if not dms_match:
            dms_match = re.search(
                r"(\d{1,2})[^\d]+(\d{1,2})[^\d]+(\d{1,2}(?:\.\d+)?)\D*([NS]).*?"
                r"(\d{1,3})[^\d]+(\d{1,2})[^\d]+(\d{1,2}(?:\.\d+)?)\D*([EW])",
                candidate_text,
                flags=re.IGNORECASE,
            )
        if dms_match:
            lat_deg = float(dms_match.group(1))
            lat_min = float(dms_match.group(2))
            lat_sec = float(dms_match.group(3))
            lat_ref = dms_match.group(4).upper()
            lon_deg = float(dms_match.group(5))
            lon_min = float(dms_match.group(6))
            lon_sec = float(dms_match.group(7))
            lon_ref = dms_match.group(8).upper()

            lat = lat_deg + lat_min / 60 + lat_sec / 3600
            lon = lon_deg + lon_min / 60 + lon_sec / 3600
            if lat_ref == "S":
                lat = -lat
            if lon_ref == "W":
                lon = -lon
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                return lat, lon

    return None, None


def normalize_location_candidate(value):
    if is_missing(value):
        return None

    text = str(value).strip()
    text = re.sub(r"https?://\S+", " ", text)
    text = re.sub(r"\bFamily (?:didn't|doesn't) know\b", " ", text, flags=re.IGNORECASE)
    text = re.sub(r"\bUnclear\b", " ", text, flags=re.IGNORECASE)
    text = re.sub(r"\bHospital in\s+", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\bburied in\s+", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\bmorgue\b", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\bcemetary\b", "cemetery", text, flags=re.IGNORECASE)
    text = re.sub(r"\bregon\b", "region", text, flags=re.IGNORECASE)
    # Supprimer les descriptions géographiques parasites (ex: "in Maritsa river")
    text = re.sub(r",?\s*\bin\s+\w+\s+(?:river|lake|sea|canal|creek)\b", "", text, flags=re.IGNORECASE)
    text = re.sub(r"[:?]", " ", text)
    text = re.sub(r"\s+", " ", text).strip(" ,.-")
    return text or None


def should_skip_place_of_death_geocoding(value):
    candidate = normalize_location_candidate(value)
    if candidate is None:
        return True
    return "region" in norm(candidate)


def geocode_with_backoff(candidate, country_hint=GEOCODER_COUNTRY_HINT):
    global last_geocode_request_ts

    # Ajouter le pays comme hint si la valeur ne le mentionne pas déjà
    if country_hint and country_hint.lower() not in candidate.lower():
        query = f"{candidate}, {country_hint}"
    else:
        query = candidate

    for attempt in range(GEOCODER_MAX_ATTEMPTS):
        elapsed = time.monotonic() - last_geocode_request_ts
        if elapsed < GEOCODER_MIN_DELAY_SECONDS:
            time.sleep(GEOCODER_MIN_DELAY_SECONDS - elapsed)

        try:
            location = geolocator.geocode(query, timeout=10)
            last_geocode_request_ts = time.monotonic()
            return location
        except GeocoderRateLimited:
            last_geocode_request_ts = time.monotonic()
            wait = GEOCODER_RATE_LIMIT_BACKOFF_SECONDS * (attempt + 1)
            if attempt < GEOCODER_MAX_ATTEMPTS - 1:
                time.sleep(wait)
                continue
            return None
        except (GeocoderTimedOut, GeocoderServiceError):
            last_geocode_request_ts = time.monotonic()
            return None
        except Exception:
            last_geocode_request_ts = time.monotonic()
            return None

    return None



def geocode_location_candidates(*values):
    for value in values:
        candidate = normalize_location_candidate(value)
        if candidate is None:
            continue
        cache_key = norm(candidate)
        if cache_key in LOCATION_COORDINATE_OVERRIDES:
            lat, lon = LOCATION_COORDINATE_OVERRIDES[cache_key]
            location_geocode_cache[cache_key] = (lat, lon)
            return lat, lon
        if cache_key in location_geocode_cache:
            lat, lon = location_geocode_cache[cache_key]
            if lat is not None and lon is not None:
                return lat, lon
            continue

        location = geocode_with_backoff(candidate)

        if location is not None:
            lat = float(location.latitude)
            lon = float(location.longitude)
            location_geocode_cache[cache_key] = (lat, lon)
            return lat, lon

        location_geocode_cache[cache_key] = (None, None)

    return None, None


def select_inhumation_geocode_candidate(*values):
    for value in values:
        candidate = normalize_location_candidate(value)
        if candidate is None:
            continue
        candidate_norm = norm(candidate)
        if any(marker in candidate_norm for marker in INHUMATION_NO_GEO_MARKERS):
            continue
        if parse_coordinates_from_text(candidate) != (None, None):
            return candidate
        if any(marker in candidate_norm for marker in INHUMATION_BURIAL_MARKERS):
            cleaned = re.sub(r"\b(?:buried|burial|inhumed|interred)\s+in\s+", "", candidate, flags=re.IGNORECASE)
            cleaned = re.sub(r"^\s*in\s+", "", cleaned, flags=re.IGNORECASE).strip(" ,.-")
            return cleaned or candidate
        tokens = candidate.split()
        if 1 <= len(tokens) <= 5:
            return candidate
    return None


def geocode_inhumation_candidate(candidate):
    if is_missing(candidate):
        return None, None
    text = str(candidate).strip()
    if not text:
        return None, None
    text_norm = norm(text)
    if any(marker in text_norm for marker in INHUMATION_NO_GEO_MARKERS):
        return None, None

    aliases = {
        "morroco": "Morocco",
        "morrocco": "Morocco",
        "cemetary": "cemetery",
    }
    lookup_value = aliases.get(text_norm, text)

    location = geocode_with_backoff(lookup_value, country_hint=None)
    if location is not None:
        return float(location.latitude), float(location.longitude)

    if re.search(r"\b(burgas|haskovo|yambol|sredets|stara zagora|vojnegovac|dimitrovgrad|sofia)\b", text_norm):
        location = geocode_with_backoff(lookup_value, country_hint=GEOCODER_COUNTRY_HINT)
        if location is not None:
            return float(location.latitude), float(location.longitude)

    return None, None


def ensure_country_node(graph, country_value):
    if is_missing(country_value):
        return None

    raw_value = str(country_value).strip()
    aliases = {
        "morroco": "Morocco",
        "morrocco": "Morocco",
        "syrian": "Syria",
        "afghan": "Afghanistan",
        "algerian": "Algeria",
    }
    lookup_value = aliases.get(norm(raw_value), raw_value)

    country = None
    try:
        country = pycountry.countries.lookup(lookup_value)
    except LookupError:
        try:
            country = pycountry.countries.search_fuzzy(lookup_value)[0]
        except LookupError:
            country = None

    if country is not None:
        country_label = getattr(country, "name", raw_value)
        country_code = getattr(country, "alpha_3", slugify(country_label).upper())
    else:
        country_label = raw_value
        country_code = slugify(raw_value).upper()

    country_uri = DATA[f"bulgarie_Country_{country_code}"]
    if (country_uri, RDF.type, F.Country) not in graph:
        graph.add((country_uri, RDF.type, F.Country))
        graph.add((country_uri, RDFS.label, Literal(country_label, lang="en")))
    return country_uri


g_ref = Graph()
g_ref.parse(ONTO_PATH, format="turtle")
g_ref.parse(THES_PATH, format="turtle")

g = Graph()
g.bind("frontlet", F)
g.bind("data", DATA)
g.bind("skos", SKOS)
g.bind("geo", GEO)
g.bind("time", TIME)
g.bind("temp", TEMP)

copy_all_class_hierarchy(g_ref, g)

geolocator = Photon(user_agent="frontlet_bulgarie_geocoder")
location_geocode_cache = {}
last_geocode_request_ts = 0.0

df = load_source_dataframe(SOURCE_PATH)
if ROW_LIMIT:
    df = df.head(ROW_LIMIT)

mapping_dict, mapping_nature = load_mapping_csv(MAPPING_PATH)
thesaurus_map = load_death_cause_thesaurus(g_ref)

PERSON_CLASS = find_by_label(g_ref, "Person") or F.Person
SOURCE_CLASS = find_by_label(g_ref, "Source") or F.Source
DEATH_EVENT_CLASS = find_by_label(g_ref, "Death") or F.Death
TRANSPORT_CLASS = find_by_label(g_ref, "Transport") or F.Transport
INHUMATION_CLASS = find_by_label(g_ref, "Inhumation") or F.Inhumation
MISSING_EVENT_CLASS = F.Missing

# Garantir que la classe Missing existe dans le schema de sortie, meme sans evenement missing instancie.
if (MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")) not in g:
    g.add((MISSING_EVENT_CLASS, RDF.type, URIRef("http://www.w3.org/2002/07/owl#Class")))
    g.add((MISSING_EVENT_CLASS, RDFS.subClassOf, F.IndividualEvent))
    if (MISSING_EVENT_CLASS, RDFS.label, None) not in g:
        g.add((MISSING_EVENT_CLASS, RDFS.label, Literal("Missing", lang="en")))

PROP_hasName = find_by_label(g_ref, "hasName") or F.hasName
PROP_gender = find_by_label(g_ref, "has gender") or F.hasGender
PROP_birthPlace = find_by_label(g_ref, "birth place") or F.birthPlace
PROP_composedOf = find_by_label(g_ref, "composedOf") or F.composedOf
PROP_hasDeathCause = find_by_label(g_ref, "hasDeathCause") or F.hasDeathCause
PROP_hasDeathNature = find_by_label(g_ref, "has death nature") or F.hasDeathNature
PROP_hasDeathCountry = find_by_label(g_ref, "has death country") or F.hasDeathCountry
PROP_transportType = find_by_label(g_ref, "transport type") or F.transportType
PROP_transportName = find_by_label(g_ref, "transport name") or F.transportName
PROP_sourcedBy = find_by_label(g_ref, "sourcedBy") or F.sourcedBy
PROP_hasComment = find_by_label(g_ref, "hasComment") or F.hasComment
PROP_temporal_before = find_by_label(g_ref, "before") or TEMP.before
PROP_temporal_after = find_by_label(g_ref, "after") or TEMP.after
PROP_yearOfBirth = find_by_label(g_ref, "year of birth") or F.yearOfBirth
PROP_hasAgeLink = find_by_label(g_ref, "aged") or F.aged

gender_uris = ensure_gender_instances(g)
ADDITIONAL_EVENT_SPECS = build_additional_event_specs(g_ref, F, find_by_label, exclude_names=["Inhumation"])

count_person = 0
count_death_events = 0
count_sources = 0
count_inhumation_events = 0
count_inhumation_geocoded = 0
count_cause_matched = 0
count_cause_from_raw = 0
count_nature_mapped = 0
count_transports = 0
count_geo_from_text = 0
count_geocoded = 0
count_geocode_skipped_region = 0
count_additional_typed_events = 0
created_transports = set()

for idx, row in df.iterrows():
    row_num = idx + 1

    name_val = get_value(row, ["Name"])
    nationality_val = get_value(row, ["Nationality ", "Nationality"])
    dob_val = get_value(row, ["DOB"])
    death_date_val = get_value(row, ["Date of death"])
    cause_val = get_value(row, ["Cause of death"])
    source_val = get_value(row, ["Source"])
    family_val = get_value(row, ["Family member/s"])
    body_location_val = get_raw_value(row, ["Body location"])
    body_location_secondary_val = get_raw_value(row, ["Body location.1"])
    place_of_death_val = get_value(row, ["Place of death"])
    text_chunks_for_typing = []
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Cause of death", "Place of death", "Body location", "Body location.1"], is_missing))
    text_chunks_for_typing.extend(collect_text_values_from_row(row, ["Source", "Family member/s"], is_missing))

    if all(
        is_missing(value)
        for value in (
            name_val,
            nationality_val,
            dob_val,
            death_date_val,
            cause_val,
            source_val,
            family_val,
            body_location_val,
            body_location_secondary_val,
            place_of_death_val,
        )
    ):
        continue

    person_uri = DATA[f"bulgarie_Person_{row_num}"]
    # Conserver une URI d'evenement deces deterministe par ligne source.
    death_event_uri = DATA[f"bulgarie_Death_{row_num}"]

    g.add((person_uri, RDF.type, PERSON_CLASS))
    g.add((person_uri, PROP_composedOf, death_event_uri))
    g.add((death_event_uri, F.livedBy, person_uri))
    g.add((person_uri, PROP_gender, gender_uris["unknown"]))
    g.add((death_event_uri, RDF.type, F.IndividualEvent))
    g.add((death_event_uri, RDF.type, DEATH_EVENT_CLASS))
    count_person += 1
    count_death_events += 1

    if not is_missing(name_val):
        g.add((person_uri, PROP_hasName, Literal(name_val)))
        g.add((person_uri, F.hasOfficialName, Literal(name_val)))

    birth_country_uri = ensure_country_node(g, nationality_val)
    if birth_country_uri is not None:
        g.add((person_uri, PROP_birthPlace, birth_country_uri))

    birth_year_literal, birth_detail = parse_birth_value(dob_val)
    if birth_year_literal is not None:
        g.add((person_uri, PROP_yearOfBirth, birth_year_literal))
    if birth_detail is not None:
        g.add((person_uri, PROP_hasComment, Literal(f"Date of Birth: {birth_detail}")))

    if not is_missing(family_val):
        g.add((person_uri, PROP_hasComment, Literal(f"Family member/s: {family_val}")))

    death_iso, death_comment = parse_date_to_iso(death_date_val)
    if death_iso is not None:
        g.add((death_event_uri, TIME.inXSDDate, Literal(death_iso, datatype=XSD.date)))
        weekday_name = infer_day_of_week_name(death_iso)
        if weekday_name:
            g.add((death_event_uri, TIME.dayOfWeek, TIME[weekday_name]))
            g.add((TIME[weekday_name], RDF.type, TIME.DayOfWeek))
            g.add((TIME[weekday_name], RDFS.label, Literal(weekday_name, lang="en")))
    if death_comment is not None:
        g.add((death_event_uri, PROP_hasComment, Literal(f"Raw death date: {death_comment}")))

    # Calculer l'age a partir de la date de naissance et de la date de deces
    if birth_year_literal is not None and death_iso is not None:
        try:
            birth_yr = int(str(birth_year_literal))
            death_yr = int(death_iso[:4])
            computed_age = death_yr - birth_yr
            if 0 <= computed_age <= 120:
                age_uri = DATA[f"bulgarie_Age_{row_num}"]
                g.add((age_uri, RDF.type, F.Age))
                g.add((age_uri, F.hasAge, Literal(computed_age, datatype=XSD.integer)))
                g.add((person_uri, PROP_hasAgeLink, age_uri))
        except (ValueError, TypeError):
            pass

    if not is_missing(place_of_death_val):
        g.add((death_event_uri, PROP_hasComment, Literal(f"Place of death: {place_of_death_val}")))

    body_location_parts = [value for value in (body_location_val, body_location_secondary_val) if str(value).strip()]
    if body_location_parts:
        g.add((death_event_uri, PROP_hasComment, Literal(f"Body location: {' | '.join(body_location_parts)}")))

    cause_uri, cause_label, cause_nature, is_literal = match_death_cause(cause_val, mapping_dict, thesaurus_map, mapping_nature)
    if cause_label is not None:
        death_cause_instance = create_or_get_death_cause_instance(g, cause_label, cause_uri)
        if death_cause_instance is not None:
            g.add((death_event_uri, PROP_hasDeathCause, death_cause_instance))
            if cause_uri is not None:
                count_cause_matched += 1
            elif is_literal:
                count_cause_from_raw += 1

    if cause_nature is not None:
        nature_norm = norm(cause_nature)
        nature_thesaurus_uri = None
        if nature_norm in ("accident", "homicide", "suicide"):
            nature_thesaurus_uri = T[nature_norm]
        elif nature_norm in ("medical", "medicale", "médical", "inconnu", "unknown"):
            nature_thesaurus_uri = T.deathNature
        death_nature_instance = create_or_get_death_nature_instance(g, cause_nature, nature_thesaurus_uri)
        if death_nature_instance is not None:
            g.add((death_event_uri, PROP_hasDeathNature, death_nature_instance))
            count_nature_mapped += 1

    transport_token = detect_transport_from_text(cause_val, place_of_death_val, body_location_val, body_location_secondary_val)
    if transport_token is not None:
        transport_uri = DATA[f"bulgarie_Transport_{slugify(transport_token)}"]
        if str(transport_uri) not in created_transports:
            g.add((transport_uri, RDF.type, TRANSPORT_CLASS))
            g.add((transport_uri, PROP_transportName, Literal(transport_token)))
            created_transports.add(str(transport_uri))
            count_transports += 1
        g.add((death_event_uri, PROP_transportType, transport_uri))

    lat, lon = parse_coordinates_from_text(place_of_death_val)
    geometry_from_text = lat is not None and lon is not None
    if not geometry_from_text:
        lat, lon = parse_coordinates_from_text(body_location_val)
        geometry_from_text = lat is not None and lon is not None
    if not geometry_from_text:
        lat, lon = parse_coordinates_from_text(body_location_secondary_val)
        geometry_from_text = lat is not None and lon is not None
    skip_place_of_death_geocoding = should_skip_place_of_death_geocoding(place_of_death_val)
    if not geometry_from_text and skip_place_of_death_geocoding:
        count_geocode_skipped_region += 1
    if not geometry_from_text and not skip_place_of_death_geocoding:
        lat, lon = geocode_location_candidates(place_of_death_val)
    geometry_geocoded_fallback = (lat is not None and lon is not None and not geometry_from_text)
    if lat is not None and lon is not None:
        geometry_uri = DATA[f"bulgarie_geometry_{row_num}"]
        g.add((death_event_uri, GEO.hasGeometry, geometry_uri))
        g.add((geometry_uri, RDF.type, GEO.Geometry))
        death_label = place_of_death_val if not is_missing(place_of_death_val) else body_location_val
        wkt = build_wkt_for_location_precision(death_label, lat, lon, geometry_geocoded_fallback)
        g.add((geometry_uri, GEO.asWKT, Literal(wkt, datatype=GEO.wktLiteral)))
        g.add((geometry_uri, F.hasPrecision, Literal(not geometry_geocoded_fallback, datatype=XSD.boolean)))
        if geometry_geocoded_fallback and death_label and not is_missing(death_label):
            g.add((death_event_uri, F.lieu, Literal(str(death_label).strip())))
        if geometry_from_text:
            count_geo_from_text += 1
        else:
            count_geocoded += 1

    if details_indicate_inhumation(body_location_val, body_location_secondary_val):
        inhumation_uri = DATA[f"bulgarie_InhumationEvent_{row_num}"]
        g.add((inhumation_uri, RDF.type, F.IndividualEvent))
        g.add((inhumation_uri, RDF.type, INHUMATION_CLASS))
        g.add((person_uri, PROP_composedOf, inhumation_uri))
        g.add((inhumation_uri, F.livedBy, person_uri))
        g.add((death_event_uri, PROP_temporal_before, inhumation_uri))
        g.add((inhumation_uri, PROP_temporal_after, death_event_uri))
        if body_location_parts:
            body_location_text = " | ".join(body_location_parts)
            g.add((inhumation_uri, PROP_hasComment, Literal(f"Body location: {body_location_text}")))

        inhumation_candidate = select_inhumation_geocode_candidate(body_location_val, body_location_secondary_val)
        if inhumation_candidate is not None:
            lat_i, lon_i = geocode_inhumation_candidate(inhumation_candidate)
            if lat_i is not None and lon_i is not None:
                inhumation_geom_uri = DATA[f"bulgarie_geometry_inhumation_{row_num}"]
                g.add((inhumation_uri, GEO.hasGeometry, inhumation_geom_uri))
                g.add((inhumation_geom_uri, RDF.type, GEO.Geometry))
                inhumation_wkt = build_wkt_for_location_precision(inhumation_candidate, lat_i, lon_i, True)
                g.add((inhumation_geom_uri, GEO.asWKT, Literal(inhumation_wkt, datatype=GEO.wktLiteral)))
                g.add((inhumation_geom_uri, F.hasPrecision, Literal(False, datatype=XSD.boolean)))
                g.add((inhumation_uri, F.lieu, Literal(str(inhumation_candidate).strip())))
                count_inhumation_geocoded += 1
            else:
                g.add((inhumation_uri, PROP_hasComment, Literal(f"Inhumation non geocodee: {inhumation_candidate}")))
        count_inhumation_events += 1

    additional_counts = add_additional_typed_events(
        g,
        [(person_uri, death_event_uri)],
        None,
        text_chunks_for_typing,
        ADDITIONAL_EVENT_SPECS,
        DATA,
        "bulgarie",
        row_num,
        F,
        RDF,
        Literal,
        PROP_composedOf,
        F.group,
        PROP_temporal_before,
        PROP_temporal_after,
        PROP_hasComment,
        PROP_hasComment,
    )
    count_additional_typed_events += sum(additional_counts.values())

    if not is_missing(source_val):
        source_uri = DATA[f"bulgarie_Source_{row_num}_{slugify(source_val)}"]
        g.add((source_uri, RDF.type, SOURCE_CLASS))
        g.add((source_uri, RDFS.label, Literal(source_val)))
        source_category = infer_source_category_key(str(source_val))
        if source_category is None:
            src_norm = norm(source_val)
            family_hints = ["family", "relative", "father", "mother", "brother", "sister"]
            civil_hints = ["mission wings", "activist", "whatsapp group", "community", "volunteer", "ngo"]
            media_hints = ["http", "www", "facebook", "twitter", "instagram", "youtube", "news", "media", "press"]
            death_cert_hints = ["death certificate", "certificat de deces", "certificado de defuncion"]
            official_hints = ["hospital", "ministry", "police", "court", "government", "consulate", "report", "verification"]

            if any(kw in src_norm for kw in death_cert_hints):
                source_category = "death_certificate"
            elif any(kw in src_norm for kw in family_hints):
                source_category = "family"
            elif any(kw in src_norm for kw in civil_hints):
                source_category = "civil_society"
            elif any(kw in src_norm for kw in media_hints):
                source_category = "media"
            elif any(kw in src_norm for kw in official_hints):
                source_category = "official_document"

        SOURCE_SUBTYPE_MAP = {
            "family": F.Family,
            "media": F.Media,
            "civil_society": F.CivilSociety,
            "death_certificate": F.DeathCertificate,
            "official_document": F.OfficialDocument,
        }
        sub_type = SOURCE_SUBTYPE_MAP.get(source_category)
        if sub_type:
            g.add((source_uri, RDF.type, sub_type))
        else:
            # Triage obligatoire: toute source est classee dans une sous-categorie autorisee.
            g.add((source_uri, RDF.type, F.OtherOfficialDocument))
        g.add((death_event_uri, PROP_sourcedBy, source_uri))
        count_sources += 1

print("\n" + "=" * 62)
print("Import Bulgarie complete")
print("=" * 62)
print(f"Rows processed                 : {len(df)}")
print(f"Persons created               : {count_person}")
print(f"Death events created          : {count_death_events}")
print(f"Inhumation events created     : {count_inhumation_events}")
print(f"Inhumation geocoded           : {count_inhumation_geocoded}")
print(f"Other typed events created    : {count_additional_typed_events}")
print(f"Sources created               : {count_sources}")
print(f"Cause instances from mapping  : {count_cause_matched}")
print(f"Cause instances from raw text : {count_cause_from_raw}")
print(f"Death nature mapped           : {count_nature_mapped}")
print(f"Transports created            : {count_transports}")
print(f"Geometry from text coords     : {count_geo_from_text}")
print(f"Geometry from geocoding       : {count_geocoded}")
print(f"Geocoding skipped (region)    : {count_geocode_skipped_region}")
count_geom_propagated = propagate_geometry_to_sibling_events(g, F, GEO, RDF, Literal, "bulgarie")
count_event_country_from_geometry = add_event_country_from_geometry(g, F, DATA, GEO, RDF, RDFS, Literal, "bulgarie")
# Completer les deces sans pays de deces avec la valeur par defaut du jeu Bulgarie.
default_death_country_uri = ensure_country_node(g, "Bulgaria")
count_default_death_country_added = 0
if default_death_country_uri is not None:
    for death_uri in g.subjects(RDF.type, DEATH_EVENT_CLASS):
        if (death_uri, PROP_hasDeathCountry, None) not in g:
            g.add((death_uri, PROP_hasDeathCountry, default_death_country_uri))
            count_default_death_country_added += 1
g.serialize(destination=OUTPUT_TTL, format="turtle")
print(f"Geometry propagated to siblings: {count_geom_propagated}")
print(f"Event countries from geometry  : {count_event_country_from_geometry}")
print(f"Default death country added    : {count_default_death_country_added}")
print("=" * 62)
print(f"Output written to: {OUTPUT_TTL}")


