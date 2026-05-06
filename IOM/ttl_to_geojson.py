#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Convertit frontlet_import_output.ttl → IOM.geojson
Un feature GeoJSON par événement individuel de décès disposant d'une géométrie.
"""

import json
import re
import os
from rdflib import Graph, Namespace, URIRef
from rdflib.namespace import RDF, RDFS, SKOS

# ----------------------- CONFIG -----------------------
INPUT_TTL  = os.path.join(os.path.dirname(__file__), "frontlet_import_output.ttl")
OUTPUT_GEOJSON = os.path.join(os.path.dirname(__file__), "IOM.geojson")

# Namespaces
F    = Namespace("http://purl.org/frontierelethale/onto/")
DATA = Namespace("http://data/frontlet/")
T    = Namespace("http://data/frontlet/thesaurus#")
GEO  = Namespace("http://www.opengis.net/ont/geosparql#")
TIME = Namespace("http://www.w3.org/2006/time#")
TEMP = Namespace("http://purl.org/frontierelethale/temporal/")
XSD  = Namespace("http://www.w3.org/2001/XMLSchema#")

# ------------------------------------------------------

def parse_wkt_point(wkt_str):
    """Extrait (longitude, latitude) depuis 'POINT(lon lat)'."""
    m = re.search(r"POINT\s*\(\s*([-\d.]+)\s+([-\d.]+)\s*\)", str(wkt_str), re.IGNORECASE)
    if not m:
        return None, None
    try:
        return float(m.group(1)), float(m.group(2))   # lon, lat
    except ValueError:
        return None, None


def uri_fragment(uri):
    """Retourne la partie locale d'une URI (après # ou dernier /)."""
    s = str(uri)
    for sep in ("#", "/"):
        if sep in s:
            return s.rsplit(sep, 1)[-1]
    return s


def first_literal(g, subject, predicate, lang=None):
    """Retourne le premier littéral trouvé (filtré par langue si précisée)."""
    for obj in g.objects(subject, predicate):
        if lang is None:
            return str(obj)
        if getattr(obj, "language", None) == lang:
            return str(obj)
    # Deuxième passe sans filtre de langue
    if lang is not None:
        for obj in g.objects(subject, predicate):
            return str(obj)
    return None


def main():
    print(f"Chargement de {INPUT_TTL} …")
    g = Graph()
    g.parse(INPUT_TTL, format="turtle")
    print(f"Graphe chargé : {len(g)} triplets.")

    # --- Pré-indexation des labels pays ---
    country_labels = {}   # country_uri -> label str
    for country_uri in g.subjects(RDF.type, F.Country):
        lbl = first_literal(g, country_uri, RDFS.label, lang="en") \
            or first_literal(g, country_uri, RDFS.label) \
            or first_literal(g, country_uri, SKOS.prefLabel)
        if lbl:
            country_labels[str(country_uri)] = lbl

    # --- Pré-indexation Person -> infos ---
    # person_uri -> { birth_countries: [...], gender: str, age: int, name: str }
    person_index = {}
    for person_uri in g.subjects(RDF.type, F.Person):
        birth_countries = [
            country_labels.get(str(c), uri_fragment(c))
            for c in g.objects(person_uri, F.birthPlace)
        ]
        gender_uri = first_literal(g, person_uri, F.gender)
        gender = uri_fragment(gender_uri) if gender_uri else None

        age = None
        for age_node in g.objects(person_uri, F.aged):
            age_val = first_literal(g, age_node, F.hasAge)
            if age_val:
                try:
                    age = int(float(age_val))
                except ValueError:
                    pass

        name = first_literal(g, person_uri, F.hasName) \
            or first_literal(g, person_uri, F.hasOfficialName) \
            or first_literal(g, person_uri, F.otherName)

        person_index[str(person_uri)] = {
            "birth_countries": birth_countries,
            "gender": gender,
            "age": age,
            "name": name,
        }

    # --- Index event -> person (inverse de composedOf) ---
    event_to_person = {}
    for person_uri in g.subjects(RDF.type, F.Person):
        for event_uri in g.objects(person_uri, F.composedOf):
            event_to_person[str(event_uri)] = str(person_uri)

    # --- Index collective events ---
    collective_index = {}   # collective_uri -> dict
    for ce_uri in g.subjects(RDF.type, F.CollectiveEvent):
        def _int(pred):
            v = first_literal(g, ce_uri, pred)
            try:
                return int(float(v)) if v else None
            except ValueError:
                return None
        collective_index[str(ce_uri)] = {
            "label": first_literal(g, ce_uri, RDFS.label),
            "number_dead": _int(F.numberDead),
            "number_survivors": _int(F.numberOfSurvivors),
            "number_missing": _int(F.numberMissing),
        }

    # --- Construire les features GeoJSON ---
    features = []
    skipped_no_geom = 0

    # Itérer sur tous les événements IndividualEvent de type Death
    death_events = set(g.subjects(RDF.type, F.Death)) & set(g.subjects(RDF.type, F.IndividualEvent))

    for event_uri in death_events:
        # Géométrie
        geom_uri = first_literal(g, event_uri, GEO.hasGeometry)
        if geom_uri is None:
            # Essayer avec URIRef
            geom_uris = list(g.objects(event_uri, GEO.hasGeometry))
            if not geom_uris:
                skipped_no_geom += 1
                continue
            geom_uri_ref = geom_uris[0]
        else:
            geom_uri_ref = URIRef(geom_uri)

        wkt = first_literal(g, geom_uri_ref, GEO.asWKT)
        if wkt is None:
            skipped_no_geom += 1
            continue

        lon, lat = parse_wkt_point(wkt)
        if lon is None or lat is None:
            skipped_no_geom += 1
            continue

        # Cause de décès
        death_cause_uri = None
        death_cause_label = None
        for dc in g.objects(event_uri, F.hasDeathCause):
            if isinstance(dc, URIRef):
                death_cause_uri = str(dc)
                death_cause_label = (
                    first_literal(g, dc, SKOS.prefLabel, lang="fr")
                    or first_literal(g, dc, SKOS.prefLabel, lang="en")
                    or first_literal(g, dc, SKOS.prefLabel)
                    or first_literal(g, dc, RDFS.label)
                    or uri_fragment(dc)
                )
            else:
                death_cause_label = str(dc)
            break

        # Date
        date_val = first_literal(g, event_uri, TIME.inXSDDate)

        # Source
        source_url = None
        source_title = None
        for src in g.objects(event_uri, F.sourcedBy):
            source_url = first_literal(g, src, F.hasWebLink)
            source_title = first_literal(g, src, RDFS.label) \
                or first_literal(g, src, F.hasComment)
            break

        # Événement collectif
        collective_info = {}
        for ce in g.objects(event_uri, F.group):
            collective_info = collective_index.get(str(ce), {})
            break

        # Personne liée
        person_info = {}
        person_uri_str = event_to_person.get(str(event_uri))
        if person_uri_str:
            person_info = person_index.get(person_uri_str, {})

        # Transport
        transport_mode = None
        for tm in g.objects(event_uri, F.transportMode):
            transport_mode = uri_fragment(tm)
            break

        # Pays de décès (frontlet:country)
        death_country = None
        for dc in g.objects(event_uri, F.country):
            death_country = country_labels.get(str(dc), uri_fragment(dc))
            break

        # Construire les propriétés
        props = {
            "event_uri": str(event_uri),
        }

        if date_val:
            props["date"] = date_val
        if death_cause_label:
            props["death_cause"] = death_cause_label
        if death_cause_uri:
            props["death_cause_uri"] = death_cause_uri
        if death_country:
            props["death_country"] = death_country
        if transport_mode:
            props["transport_mode"] = transport_mode

        # Personne
        if person_info.get("name"):
            props["name"] = person_info["name"]
        if person_info.get("gender"):
            props["gender"] = person_info["gender"]
        if person_info.get("age") is not None:
            props["age"] = person_info["age"]
        birth_countries = person_info.get("birth_countries", [])
        if birth_countries:
            props["birth_country"] = "; ".join(birth_countries)

        # Événement collectif
        if collective_info:
            if collective_info.get("number_dead") is not None:
                props["number_dead"] = collective_info["number_dead"]
            if collective_info.get("number_survivors") is not None:
                props["number_survivors"] = collective_info["number_survivors"]
            if collective_info.get("number_missing") is not None:
                props["number_missing"] = collective_info["number_missing"]

        # Source
        if source_url:
            props["source_url"] = source_url
        if source_title:
            props["source_title"] = source_title

        feature = {
            "type": "Feature",
            "geometry": {
                "type": "Point",
                "coordinates": [lon, lat],
            },
            "properties": props,
        }
        features.append(feature)

    geojson = {
        "type": "FeatureCollection",
        "features": features,
    }

    with open(OUTPUT_GEOJSON, "w", encoding="utf-8") as fh:
        json.dump(geojson, fh, ensure_ascii=False, indent=2)

    print(f"\nConversion terminée.")
    print(f"  Features créées  : {len(features)}")
    print(f"  Ignorées (sans géom.) : {skipped_no_geom}")
    print(f"  Fichier écrit    : {OUTPUT_GEOJSON}")


if __name__ == "__main__":
    main()
