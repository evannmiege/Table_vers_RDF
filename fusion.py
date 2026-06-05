"""
fusion.py

Merge 11 frontlet_import_output.ttl files into one unified Turtle file.
The script parses each input with RDFLib, merges all triples in one graph,
and writes a normalized Turtle serialization.

Usage:
    c:/Users/miegee/Desktop/22-stage/Table_vers_RDF/.venv/Scripts/python.exe fusion.py
"""

from __future__ import annotations

import sys
from pathlib import Path

from rdflib import Graph


BASE_DIR = Path(__file__).resolve().parent

SOURCE_DIR_CANDIDATES = [
    ("southern_eu",),
    ("alpes",),
    ("espagne_frontera_sur",),
    ("Italie_CPR",),
    ("Pologne",),
    ("Bosnie",),
    ("Migrant_files",),
    ("Allemagne",),
    ("fortress_europe",),
    ("Bulgarie",),
]


def resolve_input_files(base_dir: Path, dir_candidates: list[tuple[str, ...]]) -> list[Path]:
    resolved = []
    for candidates in dir_candidates:
        selected = None
        for folder_name in candidates:
            ttl_path = base_dir / folder_name / "frontlet_import_output.ttl"
            if ttl_path.exists():
                selected = ttl_path
                break
        # Keep the first candidate path to preserve explicit missing-file reporting.
        resolved.append(selected or (base_dir / candidates[0] / "frontlet_import_output.ttl"))
    return resolved


INPUT_FILES = resolve_input_files(BASE_DIR, SOURCE_DIR_CANDIDATES)
OUTPUT_FILE = BASE_DIR / "frontlet_import_output.ttl"


def merge_ttl_files(input_files: list[Path], output_file: Path) -> None:
    merged_graph = Graph()

    found_files = []
    missing_files = []

    for input_file in input_files:
        if input_file.exists():
            found_files.append(input_file)
        else:
            missing_files.append(input_file)

    if missing_files:
        print("[ERROR] Missing input files:")
        for missing in missing_files:
            print(f"  - {missing}")
        raise FileNotFoundError("One or more required TTL input files are missing.")

    for input_file in found_files:
        source_graph = Graph()
        try:
            source_graph.parse(input_file, format="turtle")
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError(f"Failed to parse Turtle file: {input_file}\nReason: {exc}") from exc

        for prefix, namespace in source_graph.namespaces():
            merged_graph.bind(prefix, namespace, replace=False)

        merged_graph += source_graph
        print(f"[OK] Parsed and merged: {input_file} ({len(source_graph)} triples)")

    merged_graph.serialize(destination=output_file, format="turtle", encoding="utf-8")
    print(f"[OK] Wrote merged Turtle: {output_file} ({len(merged_graph)} triples)")

    # Final syntax guard: re-parse the generated file to ensure Turtle validity.
    validation_graph = Graph()
    validation_graph.parse(output_file, format="turtle")
    print("[OK] Output syntax validation passed.")


def main() -> int:
    try:
        merge_ttl_files(INPUT_FILES, OUTPUT_FILE)
        return 0
    except Exception as exc:  # noqa: BLE001
        print(f"[FATAL] {exc}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
