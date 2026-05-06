#!/usr/bin/env python3

import re
import unicodedata


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

    if re.search(r"\bdeath certificate\b|\bcertificat de deces\b|\bcertificado de defuncion\b", txt):
        return "death_certificate"
    # Strip URLs before checking family/civil_society to avoid false positives
    # (e.g. a URL path containing "family" should not trigger family classification)
    txt_no_url = re.sub(r'https?://\S+', '', txt)
    if re.search(r"\bfamily\b|\bfamille\b|\bmother\b|\bfather\b|\brelative\b|\bparent\b", txt_no_url):
        return "family"
    if re.search(r"\bngo\b|\bassociation\b|\bcivil society\b|\bhuman rights\b|\bred cross\b|\bcroix rouge\b", txt_no_url):
        return "civil_society"
    if re.search(r"\bmedia\b|\bnewspaper\b|\bpress\b|\bjournal\b|\bradio\b|\btv\b|\barticle\b|\bnews\b|\bdiktyo\b", txt):
        return "media"
    # If the source is primarily a URL with no other classification, treat as media
    if re.search(r'https?://', text):
        return "media"
    if re.search(r"\bhospital\b|\bhopital\b|\bh\u00f4pital\b|\bclinic\b|\bclinique\b|\bmedical center\b|\bcentre medical\b|\bpolice\b|\bcourt\b|\bministry\b|\bofficial\b|\bgovernment\b|\bauthority\b|\breport\b", txt):
        return "official_document"
    if re.search(r"\bfacebook\b|\btwitter\b|\binstagram\b|\btiktok\b|\byoutube\b|\bsocial media\b|\breseaux sociaux\b", txt):
        return "media"

    return None