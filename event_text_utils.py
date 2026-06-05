#!/usr/bin/env python3

import re
import unicodedata
import math
import json
import time
import urllib.parse
import urllib.request

import pycountry

try:
    import reverse_geocoder as rg
except Exception:
    rg = None


def normalize_text(value):
    if value is None:
        return ""
    text = str(value).strip()
    text = unicodedata.normalize("NFKD", text)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = re.sub(r"\s+", " ", text)
    return text.lower()


def slugify_text(value):
    cleaned = re.sub(r"[^a-z0-9_]+", "_", normalize_text(value))
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    return cleaned or "unknown"


def collect_text_values_from_row(row, candidates, is_missing):
    values = []
    for name in candidates:
        # Support both pandas rows (Series) and dict rows.
        if isinstance(row, dict):
            if name not in row:
                continue
            value = row.get(name, "")
        else:
            if name not in row.index:
                continue
            value = row.get(name, "")
        if not is_missing(value):
            values.append(str(value).strip())
    return values


def build_additional_event_specs(g_ref, F, find_by_label, exclude_names=None):
    exclude_names = {str(name).strip().lower() for name in (exclude_names or [])}

    def _cls(label, fallback):
        return find_by_label(g_ref, label) or fallback

    specs = [
        {
            "name": "Inhumation",
            "class_uri": _cls("Inhumation", F.Inhumation),
            "post_mortem": True,
            "patterns": [
                r"\bburial\b", r"\bburied\b", r"\bcemetery\b", r"\bgrave\b",
                r"\binhumat", r"\binterment\b", r"\bfriedhof\b", r"\bgrab\b",
                r"\bsepolt", r"\bbeerdig",
            ],
        },
        {
            "name": "CorpseAnalysis",
            "class_uri": _cls("Corpse analysis", F.CorpseAnalysis),
            "post_mortem": True,
            "patterns": [
                r"\bautops", r"\bpost[-\s]?mortem\b", r"\bforensic\b", r"\bnecrops",
                r"\bobduktion\b", r"\bleichenschau\b", r"\banalyse du corps\b",
            ],
        },
        {
            "name": "CorpseRepatriation",
            "class_uri": _cls("Corpse repatriation", F.CorpseRepatriation),
            "post_mortem": True,
            "patterns": [
                r"\brepatriat", r"\bbody returned\b", r"\bbody.*transferred\b",
                r"\btransferred.*body\b", r"\brapatriement du corps\b", r"\bruckfuhr",
                r"\bruckfuehr", r"\bueberfuehr", r"\buberfuhr",
            ],
        },
        {
            "name": "Control",
            "class_uri": _cls("Control", F.Control),
            "post_mortem": False,
            "patterns": [
                r"\bcontrol\b", r"\bcontrole\b", r"\bcheckpoint\b", r"\bidentity check\b",
                r"\bpolice check\b", r"\bkontroll",
            ],
        },
        {
            "name": "Trace",
            "class_uri": _cls("Trace", F.Trace),
            "post_mortem": False,
            "patterns": [
                r"\btrace\b", r"\bfootprint\b", r"\bbelongings found\b", r"\bpersonal belongings\b",
                r"\babandoned object\b", r"\bobjets? (?:abandonn|laiss)", r"\bspur\b", r"\bgegenstand\b",
            ],
        },
        {
            "name": "Testimony",
            "class_uri": _cls("Testimony", F.Testimony),
            "post_mortem": False,
            "patterns": [
                r"\btestimon", r"\bwitness\b", r"\beyewitness\b", r"\btemoign", r"\bzeugen?\b",
            ],
        },
        {
            "name": "Call",
            "class_uri": _cls("Call", F.Call),
            "post_mortem": False,
            "patterns": [
                r"\bcall(?:ed|ing)?\b", r"\bphone\b", r"\btelephone\b", r"\bappel\b",
                r"\banruf\b", r"\btelefon",
            ],
        },
        {
            "name": "Conversation",
            "class_uri": _cls("Conversation", F.Conversation),
            "post_mortem": False,
            "patterns": [
                r"\bconversation\b", r"\bdiscuss(?:ed|ion)?\b", r"\btalk(?:ed|ing)?\b",
                r"\bspoke\b", r"\binterview\b", r"\bentretien\b", r"\bdiskut",
                r"\bgesprach\b", r"\bgespraech\b",
            ],
        },
    ]
    return [spec for spec in specs if spec["name"].lower() not in exclude_names]


def detect_additional_event_specs(text_chunks, specs):
    if not text_chunks:
        return []
    text = normalize_text("\n".join(text_chunks))
    found = []
    negative_trace_patterns = [
        r"\bwithout\s+(?:any\s+)?trace\b",
        r"\bwithout\s+(?:a\s+)?trace\b",
        r"\bwithour\s+(?:a\s+)?trace\b",
        r"\bno\s+trace\b",
        r"\bsans\s+trace\b",
        r"\bsin\s+rastro\b",
        r"\bsenza\s+traccia\b",
    ]

    for spec in specs:
        if spec.get("name") == "Trace":
            if any(re.search(pat, text, flags=re.IGNORECASE) for pat in negative_trace_patterns):
                continue
        for pattern in spec["patterns"]:
            if re.search(pattern, text, flags=re.IGNORECASE):
                found.append(spec)
                break
    return found


def add_additional_typed_events(
    graph,
    person_event_pairs,
    collective_event_uri,
    text_chunks,
    specs,
    data_ns,
    row_prefix,
    row_num,
    F,
    RDF,
    Literal,
    prop_composed_of,
    prop_group,
    prop_temporal_before,
    prop_temporal_after,
    prop_has_comment,
    prop_has_narrative,
):
    matched_specs = detect_additional_event_specs(text_chunks, specs)
    if not matched_specs:
        return {}

    counts = {}
    type_snippet = " | ".join(text_chunks)[:800]
    for victim_pos, (person_uri, base_event_uri) in enumerate(person_event_pairs, start=1):
        for spec in matched_specs:
            slug = slugify_text(spec["name"])
            extra_uri = data_ns[f"{row_prefix}_{slug}Event_{row_num}_{victim_pos}"]
            graph.add((extra_uri, RDF.type, spec["class_uri"]))
            graph.add((extra_uri, RDF.type, F.IndividualEvent))
            graph.add((person_uri, prop_composed_of, extra_uri))
            if collective_event_uri is not None:
                graph.add((extra_uri, prop_group, collective_event_uri))
            if spec["post_mortem"]:
                graph.add((base_event_uri, prop_temporal_before, extra_uri))
                graph.add((extra_uri, prop_temporal_after, base_event_uri))
            else:
                graph.add((extra_uri, prop_temporal_before, base_event_uri))
                graph.add((base_event_uri, prop_temporal_after, extra_uri))
            graph.add((extra_uri, prop_has_comment, Literal(f"Detected event type: {spec['name']}")))
            graph.add((extra_uri, prop_has_narrative, Literal(type_snippet)))
            counts[spec["name"]] = counts.get(spec["name"], 0) + 1
    return counts


WEEKDAY_TOKEN_TO_CANONICAL = {
    "monday": "Monday",
    "tuesday": "Tuesday",
    "wednesday": "Wednesday",
    "thursday": "Thursday",
    "friday": "Friday",
    "saturday": "Saturday",
    "sunday": "Sunday",
    "lundi": "Monday",
    "mardi": "Tuesday",
    "mercredi": "Wednesday",
    "jeudi": "Thursday",
    "vendredi": "Friday",
    "samedi": "Saturday",
    "dimanche": "Sunday",
    "lunedi": "Monday",
    "martedi": "Tuesday",
    "mercoledi": "Wednesday",
    "giovedi": "Thursday",
    "venerdi": "Friday",
    "sabato": "Saturday",
    "domenica": "Sunday",
    "montag": "Monday",
    "dienstag": "Tuesday",
    "mittwoch": "Wednesday",
    "donnerstag": "Thursday",
    "freitag": "Friday",
    "samstag": "Saturday",
    "sonntag": "Sunday",
    "poniedzialek": "Monday",
    "wtorek": "Tuesday",
    "sroda": "Wednesday",
    "czwartek": "Thursday",
    "piatek": "Friday",
    "sobota": "Saturday",
    "niedziela": "Sunday",
    "lunes": "Monday",
    "martes": "Tuesday",
    "miercoles": "Wednesday",
    "jueves": "Thursday",
    "viernes": "Friday",
    "sabado": "Saturday",
    "domingo": "Sunday",
}


def infer_day_of_week_name(*values):
    """Return canonical weekday name (Monday..Sunday) from text or parseable date values."""
    for value in values:
        if value is None:
            continue
        text = str(value).strip()
        if not text:
            continue

        normalized = normalize_text(text)
        for token, canonical in WEEKDAY_TOKEN_TO_CANONICAL.items():
            if re.search(r"\b" + re.escape(token) + r"\b", normalized):
                return canonical

        iso_match = re.search(r"\b(\d{4})-(\d{2})-(\d{2})\b", text)
        if iso_match:
            try:
                year, month, day = map(int, iso_match.groups())
                import datetime

                return datetime.date(year, month, day).strftime("%A")
            except Exception:
                pass

        eu_match = re.search(r"\b(\d{1,2})[/-](\d{1,2})[/-](\d{4})\b", text)
        if eu_match:
            try:
                day, month, year = map(int, eu_match.groups())
                import datetime

                return datetime.date(year, month, day).strftime("%A")
            except Exception:
                pass

    return None


def infer_source_category_key(*values):
    """Infer source subtype key from source free text."""
    text = "\n".join(str(v) for v in values if v is not None)
    txt = normalize_text(text)
    if txt == "":
        return None

    urls = re.findall(r'https?://[^\s"\']+', text, flags=re.IGNORECASE)
    url_hosts = []
    embedded_url_text = txt
    for url in urls:
        try:
            parsed = urllib.parse.urlparse(url)
            host = (parsed.netloc or "").lower()
            path = (parsed.path or "").lower()
            if host:
                url_hosts.append(host)
            embedded_url_text += " " + host + " " + path
        except Exception:
            continue

    media_host_patterns = (
        r'(^|\.)oko\.press$', r'(^|\.)wyborcza\.pl$', r'(^|\.)onet\.pl$',
        r'(^|\.)wprost\.pl$', r'(^|\.)euronews\.com$', r'(^|\.)euobserver\.com$',
        r'(^|\.)tvn24\.pl$', r'(^|\.)radiozet\.pl$', r'(^|\.)rmf24\.pl$',
        r'(^|\.)natemat\.pl$', r'(^|\.)spiegel\.de$', r'(^|\.)gazeta\.pl$',
        r'(^|\.)wp\.pl$', r'(^|\.)sputnik\.by$', r'(^|\.)tass\.ru$',
        r'(^|\.)bloknot\.ru$',
    )
    social_host_patterns = (r'(^|\.)facebook\.com$', r'(^|\.)twitter\.com$', r'(^|\.)instagram\.com$', r'(^|\.)tiktok\.com$', r'(^|\.)youtube\.com$')

    has_media_host = any(re.search(pattern, host) for host in url_hosts for pattern in media_host_patterns)
    has_social_host = any(re.search(pattern, host) for host in url_hosts for pattern in social_host_patterns)
    has_official_host = any(
        ".gov." in host or host.endswith(".gov") or host.endswith(".gouv.fr") or host.endswith(".gov.by")
        for host in url_hosts
    )
    has_official_channel = bool(re.search(r'\bt\.me/(gpkgovby|skgovby)\b|\bmofa\.gov\.', embedded_url_text))
    has_archive_wrapper = any(host in ("web.archive.org", "archive.ph") for host in url_hosts)
    archive_points_to_official = has_archive_wrapper and bool(re.search(r'\bgpk\.gov\.by\b|\bmofa\.gov\.', embedded_url_text))

    if re.search(r"\bdeath certificate\b|\bcertificat de deces\b|\bcertificado de defuncion\b|\bcertificado de defuncion\b|\bacta de defuncion\b", txt):
        return "death_certificate"
    # Strip URLs before checking family/civil_society to avoid false positives
    # (e.g. a URL path containing "family" should not trigger family classification)
    txt_no_url = re.sub(r'https?://\S+', '', txt)
    if re.search(r"\bfamily\b|\bfamille\b|\bfamilia\b|\bfamiliares\b|\bmother\b|\bfather\b|\bmadre\b|\bpadre\b|\brelative\b|\bparent\b", txt_no_url):
        return "family"
    if re.search(r"\bngo\b|\bassociation\b|\bcivil society\b|\bsociedad civil\b|\bhuman rights\b|\bderechos humanos\b|\bred cross\b|\bcroix rouge\b|\bamdh\b|\boim\b|\biom\b|\bunhcr\b|\bacnur\b|\bmsf\b|\bfrontex\b|\bintersos\b|\bsave the children\b|\bsos mediterranee\b|\bsos med\b|\bdoctors without borders\b|\bnrc\b|\birrc\b|\bwfp\b|\bunmiss\b|\bunhcr\b|\bunicef\b|\bamnesty\b|\bhuman rights watch\b|\bhrw\b|\bcivicam\b|\bafvic\b|\balarm phone\b|\bcaminando fronteras\b", txt_no_url):
        return "civil_society"
    if has_media_host:
        return "media"
    if has_official_host or has_official_channel or archive_points_to_official:
        return "official_document"
    if re.search(r"\bmedia\b|\bnewspaper\b|\bpress\b|\bjournal\b|\bradio\b|\btv\b|\barticle\b|\bnews\b|\bdiktyo\b", txt):
        return "media"
    if re.search(r"\bhospital\b|\bhopital\b|\bh\u00f4pital\b|\bclinic\b|\bclinique\b|\bmedical center\b|\bcentre medical\b|\bpolice\b|\bcourt\b|\bministry\b|\bofficial\b|\bgovernment\b|\bauthority\b|\breport\b|\bguardia civil\b|\bautoridades\b|\bministerio\b|\bdocumento oficial\b", txt):
        return "official_document"
    if re.search(r"\bfacebook\b|\btwitter\b|\binstagram\b|\btiktok\b|\byoutube\b|\bsocial media\b|\breseaux sociaux\b", txt):
        if has_official_channel:
            return "official_document"
        return "media"

    # If the source is primarily a URL with no clearer classification, keep the legacy fallback to media.
    if urls:
        if has_social_host and not has_official_channel:
            return "media"
        if has_archive_wrapper and not archive_points_to_official:
            return "media"
        return "media"

    # Fallback par défaut : Media (comme IOM.py)
    return "media"


def infer_imprecision_radius_km(location_label):
    """Infer a conservative radius for fallback geocoded locations.

    This is used when exact source coordinates are unavailable and the script
    falls back to name-based geocoding.
    """
    txt = normalize_text(location_label)
    if txt == "":
        return 12.0

    broad_area_patterns = [
        r"\bregion\b", r"\bprovince\b", r"\bdistrict\b", r"\bgovernorate\b",
        r"\bstate\b", r"\bcountry\b", r"\bborder\b", r"\bfrontier\b",
        r"\bsea\b", r"\bocean\b", r"\bdesert\b",
    ]
    medium_area_patterns = [
        r"\bcity\b", r"\btown\b", r"\bvillage\b", r"\bmunicipality\b",
        r"\bcommune\b", r"\bquartier\b", r"\bneighbou?rhood\b", r"\bzona\b",
    ]
    fine_area_patterns = [
        r"\bcemetery\b", r"\bhospital\b", r"\bchurch\b", r"\bport\b",
        r"\bharbour\b", r"\bbeach\b", r"\bcamp\b", r"\bstation\b",
        r"\bstreet\b", r"\bavenue\b", r"\broad\b",
    ]

    if any(re.search(p, txt, flags=re.IGNORECASE) for p in broad_area_patterns):
        return 35.0
    if any(re.search(p, txt, flags=re.IGNORECASE) for p in medium_area_patterns):
        return 14.0
    if any(re.search(p, txt, flags=re.IGNORECASE) for p in fine_area_patterns):
        return 5.0
    return 10.0


def build_bbox_polygon_wkt(lat, lon, radius_km):
    """Build a square POLYGON WKT centered on (lat, lon) with radius in km."""
    lat_f = float(lat)
    lon_f = float(lon)
    radius = max(0.1, float(radius_km))

    lat_delta = radius / 111.0
    cos_lat = math.cos(math.radians(lat_f))
    lon_delta = radius / (111.0 * max(0.2, abs(cos_lat)))

    min_lat = lat_f - lat_delta
    max_lat = lat_f + lat_delta
    min_lon = lon_f - lon_delta
    max_lon = lon_f + lon_delta

    return (
        f"POLYGON(({min_lon} {min_lat}, {max_lon} {min_lat}, "
        f"{max_lon} {max_lat}, {min_lon} {max_lat}, {min_lon} {min_lat}))"
    )


_boundary_wkt_cache = {}
_boundary_last_lookup_ts = 0.0
_boundary_lookup_min_delay_sec = 1.2


def _throttle_boundary_lookup():
    global _boundary_last_lookup_ts
    elapsed = time.time() - _boundary_last_lookup_ts
    if elapsed < _boundary_lookup_min_delay_sec:
        time.sleep(_boundary_lookup_min_delay_sec - elapsed)
    _boundary_last_lookup_ts = time.time()


def load_boundary_wkt_cache(path):
    """Load the persistent boundary WKT cache from a JSON file on disk."""
    global _boundary_wkt_cache
    try:
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                _boundary_wkt_cache.update(data)
    except Exception:
        pass


def save_boundary_wkt_cache(path):
    """Save the boundary WKT cache to a JSON file on disk."""
    try:
        os.makedirs(os.path.dirname(path) if os.path.dirname(path) else ".", exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(_boundary_wkt_cache, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def _geojson_polygon_or_multipolygon_to_wkt(geometry):
    if not geometry or not isinstance(geometry, dict):
        return None
    gtype = geometry.get("type")
    coords = geometry.get("coordinates")
    if not coords:
        return None

    def ring_to_wkt(ring):
        if not isinstance(ring, list) or len(ring) < 4:
            return None
        pts = []
        for coord in ring:
            if not isinstance(coord, (list, tuple)) or len(coord) < 2:
                continue
            lon = coord[0]
            lat = coord[1]
            try:
                lon_f = float(lon)
                lat_f = float(lat)
            except Exception:
                continue
            if not (math.isfinite(lat_f) and math.isfinite(lon_f)):
                continue
            pts.append(f"{lon_f} {lat_f}")
        if len(pts) < 4:
            return None
        return "(" + ", ".join(pts) + ")"

    if gtype == "Polygon":
        rings = []
        for ring in coords:
            ring_wkt = ring_to_wkt(ring)
            if ring_wkt is not None:
                rings.append(ring_wkt)
        if not rings:
            return None
        return "POLYGON(" + ", ".join(rings) + ")"

    if gtype == "MultiPolygon":
        polygons = []
        for poly in coords:
            if not isinstance(poly, list):
                continue
            rings = []
            for ring in poly:
                ring_wkt = ring_to_wkt(ring)
                if ring_wkt is not None:
                    rings.append(ring_wkt)
            if rings:
                polygons.append("(" + ", ".join(rings) + ")")
        if not polygons:
            return None
        return "MULTIPOLYGON(" + ", ".join(polygons) + ")"

    return None


def _build_circle_polygon_wkt(lat, lon, radius_km=1.2, vertices=28):
    """Build a non-square fallback polygon centered on a point."""
    try:
        lat_f = float(lat)
        lon_f = float(lon)
        radius_km_f = float(radius_km)
    except Exception:
        return None
    if not (math.isfinite(lat_f) and math.isfinite(lon_f) and radius_km_f > 0):
        return None

    # Approximate conversion from km to degrees around latitude.
    lat_deg = radius_km_f / 111.0
    cos_lat = math.cos((lat_f * math.pi) / 180.0)
    lon_deg = radius_km_f / (111.0 * max(0.2, abs(cos_lat)))

    pts = []
    n = max(10, int(vertices))
    for i in range(n):
        theta = 2.0 * math.pi * (i / n)
        py = lat_f + (lat_deg * math.sin(theta))
        px = lon_f + (lon_deg * math.cos(theta))
        pts.append(f"{px} {py}")
    # Close the ring.
    pts.append(pts[0])
    return "POLYGON((" + ", ".join(pts) + "))"


def _fallback_radius_km_for_label(location_label):
    txt = normalize_text(location_label)
    if txt == "":
        return 2.0
    if re.search(r"\b(playa|beach|plage|quartier|neighbou?rhood|barrio|sarchal|ribera|puerto|port)\b", txt):
        return 0.8
    if re.search(r"\b(city|ville|ciudad|town|commune|municipality|ceuta|melilla)\b", txt):
        return 4.0
    if re.search(r"\b(region|province|provincia|county|state)\b", txt):
        return 9.0
    if re.search(r"\b(country|pays|espana|spain|marruecos|morocco|mauritania|senegal)\b", txt):
        return 14.0
    return 2.2


def _compute_bounds_from_geojson(geometry):
    if not geometry or not isinstance(geometry, dict):
        return None
    coords = geometry.get("coordinates")
    if not coords:
        return None

    min_lat = float("inf")
    max_lat = float("-inf")
    min_lon = float("inf")
    max_lon = float("-inf")

    def _walk(node):
        nonlocal min_lat, max_lat, min_lon, max_lon
        if not isinstance(node, list) or len(node) == 0:
            return
        if isinstance(node[0], (int, float)) and len(node) >= 2:
            try:
                lon = float(node[0])
                lat = float(node[1])
            except Exception:
                return
            if not (math.isfinite(lat) and math.isfinite(lon)):
                return
            min_lat = min(min_lat, lat)
            max_lat = max(max_lat, lat)
            min_lon = min(min_lon, lon)
            max_lon = max(max_lon, lon)
            return
        for child in node:
            _walk(child)

    _walk(coords)
    if not all(math.isfinite(v) for v in (min_lat, max_lat, min_lon, max_lon)):
        return None
    return {
        "min_lat": min_lat,
        "max_lat": max_lat,
        "min_lon": min_lon,
        "max_lon": max_lon,
    }


def _approx_area_km2(bounds):
    if not bounds:
        return float("inf")
    lat_span = max(0.0, float(bounds["max_lat"]) - float(bounds["min_lat"]))
    lon_span = max(0.0, float(bounds["max_lon"]) - float(bounds["min_lon"]))
    mid_lat = (float(bounds["max_lat"]) + float(bounds["min_lat"])) / 2.0
    cos_lat = math.cos((mid_lat * math.pi) / 180.0)
    lat_km = lat_span * 111.0
    lon_km = lon_span * 111.0 * max(0.2, abs(cos_lat))
    return max(0.01, lat_km * lon_km)


def _normalize_feature_type(props):
    if not isinstance(props, dict):
        return ""
    addresstype = str(props.get("addresstype", "")).strip().lower()
    ftype = str(props.get("type", "")).strip().lower()
    return addresstype or ftype


def _score_boundary_feature(feature):
    if not isinstance(feature, dict):
        return -10**9
    geometry = feature.get("geometry")
    if not isinstance(geometry, dict):
        return -10**9
    if geometry.get("type") not in ("Polygon", "MultiPolygon"):
        return -10**9

    props = feature.get("properties") if isinstance(feature.get("properties"), dict) else {}
    ftype = _normalize_feature_type(props)
    fclass = str(props.get("class", props.get("category", ""))).strip().lower()

    # Base score for polygon candidates.
    score = 100.0

    preferred = {
        "beach": 180,
        "neighbourhood": 170,
        "suburb": 160,
        "quarter": 160,
        "hamlet": 150,
        "village": 140,
        "town": 130,
        "municipality": 120,
        "city": 110,
        "island": 100,
        "county": 65,
        "state": 50,
    }
    if ftype in preferred:
        score += preferred[ftype]

    if ftype in {"country", "region", "province", "sea", "ocean", "water"}:
        score -= 260

    if fclass in {"highway", "railway", "public_transport"}:
        score -= 300

    if fclass == "amenity" and ftype in {"bus_station", "station", "platform"}:
        score -= 280

    bounds = _compute_bounds_from_geojson(geometry)
    area_km2 = _approx_area_km2(bounds)
    # Penalize very large polygons to avoid country-level contours when not needed.
    score -= min(260.0, math.log10(area_km2 + 1.0) * 35.0)

    return score


def _pick_best_polygon_geometry(features, lat=None, lon=None):
    """Pick the best polygon geometry from a list of Nominatim features.

    If lat/lon are provided, only polygons whose bounding box contains (or nearly contains)
    the point are eligible. This prevents geocoding Cartagena Spain but getting a polygon from
    Cartagena Colombia, for example.
    """
    if not isinstance(features, list) or len(features) == 0:
        return None

    best_geom = None
    best_score = -10**9
    SPATIAL_MARGIN_DEG = 1.5  # degrees tolerance for bounding box containment check

    for feat in features:
        score = _score_boundary_feature(feat)
        if score <= best_score:
            continue
        geom = feat.get("geometry") if isinstance(feat, dict) else None
        if not isinstance(geom, dict):
            continue
        if geom.get("type") not in ("Polygon", "MultiPolygon"):
            continue
        # Spatial filter: reject polygons whose bounding box does not contain the geocoded point.
        if lat is not None and lon is not None:
            bounds = _compute_bounds_from_geojson(geom)
            if bounds:
                if not (
                    bounds["min_lat"] - SPATIAL_MARGIN_DEG <= lat <= bounds["max_lat"] + SPATIAL_MARGIN_DEG
                    and bounds["min_lon"] - SPATIAL_MARGIN_DEG <= lon <= bounds["max_lon"] + SPATIAL_MARGIN_DEG
                ):
                    continue  # This polygon is spatially inconsistent with the geocoded point
        best_score = score
        best_geom = geom

    if not isinstance(best_geom, dict):
        return None
    if best_geom.get("type") not in ("Polygon", "MultiPolygon"):
        return None
    return best_geom


def _build_boundary_query_candidates(label):
    txt = str(label or "").strip()
    if txt == "":
        return []

    candidates = [txt]
    stripped = re.sub(r"^playa\s+de\s+(la|el|los|las)\s+", "", txt, flags=re.IGNORECASE).strip()
    if stripped and normalize_text(stripped) != normalize_text(txt):
        candidates.append(stripped)

    # Split forms like "la Ribera - Ceuta" and "Foo, Bar" to allow admin fallback.
    for sep in [",", "-"]:
        if sep in txt:
            parts = [p.strip() for p in txt.split(sep) if p and p.strip()]
            for p in reversed(parts):
                if len(p) >= 3:
                    candidates.append(p)

    out = []
    seen = set()
    for c in candidates:
        k = normalize_text(c)
        if k and k not in seen:
            seen.add(k)
            out.append(c)
    return out


def _nominatim_search_features(query_text, limit=12):
    q = urllib.parse.quote(str(query_text or "").strip())
    url = (
        "https://nominatim.openstreetmap.org/search?format=geojson"
        f"&polygon_geojson=1&addressdetails=1&limit={int(limit)}&q=" + q
    )
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "frontlet-table2rdf-boundary/1.0",
            "Accept": "application/geo+json, application/json",
            "Accept-Language": "fr,en;q=0.8",
        },
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        payload = resp.read().decode("utf-8", errors="replace")
    data = json.loads(payload)
    if not isinstance(data, dict):
        return []
    feats = data.get("features", [])
    return feats if isinstance(feats, list) else []


def _nominatim_reverse_city_label(lat, lon):
    try:
        qlat = urllib.parse.quote(str(float(lat)))
        qlon = urllib.parse.quote(str(float(lon)))
    except Exception:
        return None

    url = (
        "https://nominatim.openstreetmap.org/reverse?format=jsonv2"
        f"&lat={qlat}&lon={qlon}&zoom=10&addressdetails=1"
    )
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "frontlet-table2rdf-boundary/1.0",
            "Accept": "application/json",
            "Accept-Language": "fr,en;q=0.8",
        },
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        payload = resp.read().decode("utf-8", errors="replace")
    data = json.loads(payload)
    if not isinstance(data, dict):
        return None
    addr = data.get("address") if isinstance(data.get("address"), dict) else {}
    for key in ("city", "town", "municipality", "county", "state"):
        v = addr.get(key)
        if isinstance(v, str) and v.strip() != "":
            return v.strip()
    return None


def fetch_boundary_wkt_for_location(location_label, lat=None, lon=None):
    """Fetch an administrative boundary polygon from Nominatim as WKT."""
    label = str(location_label or "").strip()
    if label == "":
        return None

    cache_key = normalize_text(label)
    if lat is not None and lon is not None:
        try:
            cache_key += f"|{float(lat):.4f}|{float(lon):.4f}"
        except Exception:
            pass
    if cache_key in _boundary_wkt_cache:
        return _boundary_wkt_cache[cache_key]

    _throttle_boundary_lookup()
    try:
        query_candidates = _build_boundary_query_candidates(label)

        geom = None
        for candidate in query_candidates:
            features = _nominatim_search_features(candidate, limit=12)
            # Pass lat/lon so only spatially consistent polygons are accepted
            geom = _pick_best_polygon_geometry(features, lat=lat, lon=lon)
            if geom is not None:
                break

        # Fallback: reverse geocode point to nearest admin unit (e.g., Ceuta)
        # to ensure an enclosing, coherent polygon when micro-toponym is missing.
        if geom is None and lat is not None and lon is not None:
            admin_label = _nominatim_reverse_city_label(lat, lon)
            if admin_label:
                features = _nominatim_search_features(admin_label, limit=12)
                geom = _pick_best_polygon_geometry(features, lat=lat, lon=lon)

        wkt = _geojson_polygon_or_multipolygon_to_wkt(geom)
        _boundary_wkt_cache[cache_key] = wkt
        return wkt
    except Exception:
        _boundary_wkt_cache[cache_key] = None
        return None


def build_wkt_for_location_precision(location_label, lat, lon, is_geocoded_fallback):
    """Return POINT for precise coordinates; polygon contour for geocoded fallback when available."""
    lat_f = float(lat)
    lon_f = float(lon)

    if bool(is_geocoded_fallback):
        # Renforcer la recherche de polygones OSM
        boundary_wkt = fetch_boundary_wkt_for_location(location_label, lat=lat_f, lon=lon_f)
        if boundary_wkt:
            return boundary_wkt

        # Supprimer les cercles comme fallback
        # Si aucun polygone n'est trouvé, retourner directement un POINT
        print(f"⚠️ Aucun polygone trouvé pour '{location_label}' ({lat_f}, {lon_f}). Utilisation d'un POINT.")
        return f"POINT({lon_f} {lat_f})"

    # Si les coordonnées sont précises, retourner un POINT directement
    return f"POINT({lon_f} {lat_f})"


def force_local_area_wkt_from_point(location_label, lat, lon):
    """Force a non-square local area polygon from a point, using label-based radius."""
    lat_f = float(lat)
    lon_f = float(lon)
    radius_km = _fallback_radius_km_for_label(location_label)
    forced = _build_circle_polygon_wkt(lat_f, lon_f, radius_km=radius_km, vertices=28)
    if forced:
        return forced
    return f"POINT({lon_f} {lat_f})"

def propagate_geometry_to_sibling_events(graph, F, GEO, RDF, Literal, dataset_slug):
    """Propagation volontairement désactivée.

    Les événements ante/post mortem (inhumation, trace, appel, etc.) doivent
    garder leurs propres localisations et ne pas hériter des coordonnées de décès.
    """
    return 0


def build_cemetery_geocode_cache(commune_list, geocoder=None, country_hint_map=None):
    """
    Geocode cimeteries (graveyards) for given communes.
    
    Args:
        commune_list: List of commune names to geocode
        geocoder: geopy Photon geocoder instance
        country_hint_map: Optional dict mapping commune -> country name for better results
    
    Returns:
        dict: {commune: (lat, lon)} for cemetery locations
    """
    if geocoder is None:
        return {}
    
    cache = {}
    for commune in commune_list:
        if not commune or commune in cache:
            continue
        
        commune = str(commune).strip()
        try:
            # Rechercher "cimetière, commune" ou "cemetery, commune"
            search_terms = [
                f"cimetière, {commune}",
                f"cemetery, {commune}",
                f"cimetiere, {commune}",
            ]
            
            # Ajouter le hint de pays si disponible
            if country_hint_map and commune in country_hint_map:
                country = country_hint_map[commune]
                search_terms = [f"{term}, {country}" for term in search_terms]
            
            result = None
            for search_term in search_terms:
                try:
                    locations = geocoder.geocode(search_term, timeout=5, exactly_one=True)
                    if locations:
                        result = locations
                        break
                except Exception:
                    continue
            
            if result:
                cache[commune] = (result.latitude, result.longitude)
            else:
                cache[commune] = (None, None)
        except Exception:
            cache[commune] = (None, None)
    
    return cache


_COORD_COUNTRY_CACHE = {}
_BLOCKED_EVENT_COUNTRY_CODES = {"EH"}
_BLOCKED_EVENT_COUNTRY_LABELS = {
    "sahrawi arab democratic republic",
    "republique sahraouie",
    "republique sahraoui",
    "western sahara",
}


def _parse_point_wkt(wkt_literal):
    text = str(wkt_literal).strip()
    match = re.search(
        r"POINT\s*\(\s*([-+]?\d+(?:\.\d+)?)\s+([-+]?\d+(?:\.\d+)?)\s*\)",
        text,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    lon = float(match.group(1))
    lat = float(match.group(2))
    if lat < -90.0 or lat > 90.0 or lon < -180.0 or lon > 180.0:
        return None
    return (lat, lon)


def _country_name_from_coordinates(lat, lon):
    key = (round(lat, 4), round(lon, 4))
    if key in _COORD_COUNTRY_CACHE:
        return _COORD_COUNTRY_CACHE[key]

    if rg is None:
        _COORD_COUNTRY_CACHE[key] = None
        return None

    country_name = None
    try:
        results = rg.search([(lat, lon)], mode=1)
        if results:
            cc = (results[0].get("cc") or "").strip().upper()
            if cc:
                country = pycountry.countries.get(alpha_2=cc)
                if country is not None:
                    country_name = getattr(country, "name", None)
    except Exception:
        country_name = None

    _COORD_COUNTRY_CACHE[key] = country_name
    return country_name


def add_event_country_from_geometry(graph, F, DATA, GEO, RDF, RDFS, Literal, dataset_slug):
    """Attach hasDeathCountry to individual events using geometry coordinates.
    If no usable coordinates are available, no country is added."""
    count = 0
    prop_has_death_country = F.hasDeathCountry
    class_death_country = F.DeathCountry
    class_country = F.Country

    for event_uri in set(graph.subjects(RDF.type, F.IndividualEvent)):
        if (event_uri, prop_has_death_country, None) in graph:
            continue

        country_name = None
        for geom_uri in graph.objects(event_uri, GEO.hasGeometry):
            for wkt_literal in graph.objects(geom_uri, GEO.asWKT):
                coords = _parse_point_wkt(wkt_literal)
                if coords is None:
                    continue
                country_name = _country_name_from_coordinates(coords[0], coords[1])
                if country_name:
                    break
            if country_name:
                break

        if not country_name:
            continue

        try:
            country_obj = pycountry.countries.lookup(country_name)
            country_label = getattr(country_obj, "name", country_name)
            country_code = getattr(country_obj, "alpha_3", slugify_text(country_label).upper())
            country_alpha2 = getattr(country_obj, "alpha_2", "")
        except Exception:
            country_label = country_name
            country_code = slugify_text(country_name).upper()
            country_alpha2 = ""

        if country_alpha2 in _BLOCKED_EVENT_COUNTRY_CODES:
            continue
        if normalize_text(country_label) in _BLOCKED_EVENT_COUNTRY_LABELS:
            continue

        if not country_code:
            continue

        country_uri = DATA[f"{dataset_slug}_DeathCountry_{country_code}"]
        if (country_uri, RDF.type, class_death_country) not in graph:
            graph.add((country_uri, RDF.type, class_death_country))
            graph.add((country_uri, RDF.type, class_country))
            graph.add((country_uri, RDFS.label, Literal(country_label, lang="en")))

        graph.add((event_uri, prop_has_death_country, country_uri))
        count += 1

    return count