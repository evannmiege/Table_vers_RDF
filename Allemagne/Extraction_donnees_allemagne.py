import argparse
import csv
import json
import time
from datetime import date
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import requests


API_BASE = "https://ari-dok.org/ari-db/"
SEARCH_URL = API_BASE + "search/?mode=json&format=json"
DATE_RANGE_URL = API_BASE + "docu_date_range/?format=json"
ENTRY_URL_TEMPLATE = API_BASE + "entry/{pk}/?format=json"


def parse_iso_date(value: str) -> date:
	year, month, day = map(int, value.split("-"))
	return date(year, month, day)


def build_five_year_windows(start: date, end: date) -> List[Tuple[date, date]]:
	windows: List[Tuple[date, date]] = []
	current_start = start

	while current_start <= end:
		current_end_year = min(current_start.year + 4, end.year)
		current_end = date(current_end_year, 12, 31)
		if current_end > end:
			current_end = end
		windows.append((current_start, current_end))
		current_start = date(current_end.year + 1, 1, 1)

	return windows


def post_search(session: requests.Session, start: date, end: date, timeout: int) -> List[Dict]:
	payload = {"date": [start.isoformat(), end.isoformat()]}
	response = session.post(SEARCH_URL, json=payload, timeout=timeout)
	response.raise_for_status()
	data = response.json()
	if not isinstance(data, list):
		raise ValueError(f"Unexpected payload for {start} to {end}: {type(data)}")
	return data


def split_window(start: date, end: date) -> Tuple[Tuple[date, date], Tuple[date, date]]:
	mid_year = (start.year + end.year) // 2
	left = (start, date(mid_year, 12, 31))
	right = (date(mid_year + 1, 1, 1), end)
	return left, right


def fetch_window_resilient(
	session: requests.Session,
	start: date,
	end: date,
	timeout: int,
	sleep_seconds: float,
	retries: int,
) -> List[Dict]:
	for attempt in range(1, retries + 1):
		try:
			return post_search(session, start, end, timeout)
		except (requests.RequestException, ValueError) as exc:
			is_last_try = attempt == retries
			print(f"  Tentative {attempt}/{retries} echouee pour {start} -> {end}: {exc}")
			if not is_last_try:
				time.sleep(sleep_seconds * attempt)

	if start.year == end.year:
		print(f"  Abandon de la tranche {start} -> {end} apres {retries} tentatives")
		return []

	left, right = split_window(start, end)
	print(f"  Decoupage en sous-tranches: {left[0]}->{left[1]} et {right[0]}->{right[1]}")
	left_rows = fetch_window_resilient(session, left[0], left[1], timeout, sleep_seconds, retries)
	right_rows = fetch_window_resilient(session, right[0], right[1], timeout, sleep_seconds, retries)
	return left_rows + right_rows


def fetch_all_entries(timeout: int = 60, sleep_seconds: float = 0.3, retries: int = 3) -> List[Dict]:
	session = requests.Session()
	session.headers.update({"User-Agent": "Table_vers_RDF/ARI-fetcher"})

	date_range_response = session.get(DATE_RANGE_URL, timeout=timeout)
	date_range_response.raise_for_status()
	date_range = date_range_response.json()
	lower_date = parse_iso_date(date_range["lower_date"])
	upper_date = parse_iso_date(date_range["upper_date"])

	windows = build_five_year_windows(lower_date, upper_date)
	print(f"Plage documentaire: {lower_date} -> {upper_date}")
	print(f"Decoupage en {len(windows)} tranches (max 5 ans)")

	dedup: Dict[int, Dict] = {}
	for idx, (start, end) in enumerate(windows, start=1):
		print(f"[{idx}/{len(windows)}] Requete {start} -> {end}")
		rows = fetch_window_resilient(
			session=session,
			start=start,
			end=end,
			timeout=timeout,
			sleep_seconds=sleep_seconds,
			retries=retries,
		)

		print(f"  {len(rows)} enregistrements recuperes")
		for row in rows:
			pk = row.get("pk")
			if pk is not None:
				dedup[pk] = row

		time.sleep(sleep_seconds)

	print(f"Total unique (par pk): {len(dedup)}")
	return list(dedup.values())


def _to_clean_text(value) -> str:
	if value is None:
		return ""
	return str(value).replace("\r\n", "\n").replace("\r", "\n").strip()


def _summaries_to_text(entry_detail: Dict) -> str:
	summaries = entry_detail.get("summaries") or []
	chunks: List[str] = []
	for item in summaries:
		if not isinstance(item, dict):
			continue
		title = _to_clean_text(item.get("title"))
		info_text = _to_clean_text(item.get("info_text"))
		if title and info_text:
			chunks.append(f"{title}: {info_text}")
		elif info_text:
			chunks.append(info_text)
		elif title:
			chunks.append(title)
	return "\n\n".join(chunks)


def _sources_to_text(entry_detail: Dict) -> str:
	sources = entry_detail.get("sources") or []
	parts: List[str] = []
	for src in sources:
		if not isinstance(src, dict):
			continue
		text = _to_clean_text(src.get("text"))
		link = _to_clean_text(src.get("link"))
		title = _to_clean_text(src.get("title"))
		candidate = " | ".join([p for p in [text, title, link] if p])
		if candidate:
			parts.append(candidate)
	return " || ".join(parts)


def fetch_entry_detail(session: requests.Session, pk: int, timeout: int, retries: int) -> Dict:
	url = ENTRY_URL_TEMPLATE.format(pk=pk)
	for attempt in range(1, retries + 1):
		try:
			response = session.get(url, timeout=timeout)
			response.raise_for_status()
			data = response.json()
			if isinstance(data, dict):
				return data
			raise ValueError(f"Payload detail inattendu pour pk={pk}: {type(data)}")
		except (requests.RequestException, ValueError):
			if attempt == retries:
				return {}
	return {}


def enrich_entries_with_details(
	entries: List[Dict],
	timeout: int,
	retries: int,
	detail_sleep: float,
	details_max: int | None,
) -> List[Dict]:
	session = requests.Session()
	session.headers.update({"User-Agent": "Table_vers_RDF/ARI-fetcher-details"})

	total = len(entries) if details_max is None else min(len(entries), details_max)
	print(f"Recuperation des details narratifs pour {total} entrees...")

	enriched: List[Dict] = []
	for i, base_entry in enumerate(entries, start=1):
		if details_max is not None and i > details_max:
			enriched.append(dict(base_entry))
			continue

		pk = base_entry.get("pk")
		detail = fetch_entry_detail(session, pk, timeout=timeout, retries=retries) if pk is not None else {}

		entry = dict(base_entry)
		entry["info_text"] = _to_clean_text(detail.get("info_text"))
		entry["narrative_text"] = entry["info_text"]
		entry["summaries_text"] = _summaries_to_text(detail)
		entry["sources_text"] = _sources_to_text(detail)
		entry["city_name"] = _to_clean_text((detail.get("city") or {}).get("name")) if isinstance(detail.get("city"), dict) else ""
		entry["state_name"] = _to_clean_text((detail.get("state") or {}).get("name")) if isinstance(detail.get("state"), dict) else ""

		enriched.append(entry)

		if i % 250 == 0 or i == total:
			print(f"  details: {min(i, total)}/{total}")

		if detail_sleep > 0:
			time.sleep(detail_sleep)

	return enriched


def flatten_categories(entry: Dict) -> str:
	categories = entry.get("categories") or []
	labels: List[str] = []
	for cat in categories:
		cat_type = cat.get("type") or {}
		name = cat_type.get("name")
		if name:
			labels.append(str(name))
	return "|".join(labels)


def flatten_country_origin(entry: Dict) -> str:
	countries = entry.get("country_of_origin") or []
	names = [c.get("name") for c in countries if isinstance(c, dict) and c.get("name")]
	return "|".join(names)


def write_json(entries: Iterable[Dict], output_path: Path) -> None:
	output_path.parent.mkdir(parents=True, exist_ok=True)
	with output_path.open("w", encoding="utf-8") as fh:
		json.dump(list(entries), fh, ensure_ascii=False, indent=2)


def write_csv(entries: Iterable[Dict], output_path: Path) -> None:
	output_path.parent.mkdir(parents=True, exist_ok=True)
	fieldnames = [
		"pk",
		"ari_id",
		"title",
		"date",
		"location_custom_name",
		"latitude",
		"longitude",
		"categories",
		"country_of_origin",
		"narrative_text",
		"info_text",
		"summaries_text",
		"sources_text",
		"city_name",
		"state_name",
		"href",
	]

	with output_path.open("w", newline="", encoding="utf-8") as fh:
		writer = csv.DictWriter(fh, fieldnames=fieldnames)
		writer.writeheader()

		for e in entries:
			coord = e.get("coord") or [None, None]
			lat = coord[0] if len(coord) > 0 else None
			lon = coord[1] if len(coord) > 1 else None

			writer.writerow(
				{
					"pk": e.get("pk"),
					"ari_id": e.get("ari_id"),
					"title": e.get("title"),
					"date": e.get("date"),
					"location_custom_name": e.get("location_custom_name"),
					"latitude": lat,
					"longitude": lon,
					"categories": flatten_categories(e),
					"country_of_origin": flatten_country_origin(e),
					"narrative_text": e.get("narrative_text") or e.get("info_text") or "",
					"info_text": e.get("info_text") or "",
					"summaries_text": e.get("summaries_text") or "",
					"sources_text": e.get("sources_text") or "",
					"city_name": e.get("city_name") or "",
					"state_name": e.get("state_name") or "",
					"href": e.get("href"),
				}
			)


def parse_args() -> argparse.Namespace:
	parser = argparse.ArgumentParser(
		description="Recupere les donnees de la carte ARI et exporte en JSON/CSV."
	)
	parser.add_argument(
		"--out-dir",
		default="ari_dok_export",
		help="Dossier de sortie (defaut: ari_dok_export)",
	)
	parser.add_argument(
		"--timeout",
		type=int,
		default=60,
		help="Timeout HTTP en secondes (defaut: 60)",
	)
	parser.add_argument(
		"--sleep",
		type=float,
		default=0.3,
		help="Pause entre requetes (defaut: 0.3)",
	)
	parser.add_argument(
		"--retries",
		type=int,
		default=3,
		help="Nombre de tentatives HTTP par tranche (defaut: 3)",
	)
	parser.add_argument(
		"--with-details",
		action="store_true",
		help="Recuperer le detail complet de chaque entree (info_text, summaries, sources).",
	)
	parser.add_argument(
		"--details-sleep",
		type=float,
		default=0.0,
		help="Pause entre requetes detail (defaut: 0.0)",
	)
	parser.add_argument(
		"--details-max",
		type=int,
		default=None,
		help="Limiter le nombre de details recuperes (debug).",
	)
	return parser.parse_args()


def main() -> None:
	args = parse_args()
	out_dir = Path(args.out_dir)

	entries = fetch_all_entries(timeout=args.timeout, sleep_seconds=args.sleep, retries=args.retries)
	if args.with_details:
		entries = enrich_entries_with_details(
			entries=entries,
			timeout=args.timeout,
			retries=args.retries,
			detail_sleep=args.details_sleep,
			details_max=args.details_max,
		)
	entries_sorted = sorted(entries, key=lambda x: (x.get("date") or "", x.get("pk") or 0))

	json_path = out_dir / "ari_dok_entries.json"
	csv_path = out_dir / "ari_dok_entries.csv"

	write_json(entries_sorted, json_path)
	write_csv(entries_sorted, csv_path)

	print(f"Export JSON: {json_path}")
	print(f"Export CSV : {csv_path}")


if __name__ == "__main__":
	main()
