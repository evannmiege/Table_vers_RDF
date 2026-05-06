#!/usr/bin/env python3
"""
Smoke-test runner: exécute chaque script avec un timeout de 90s.
Affiche uniquement les lignes de résumé (created/processed/complete/Error/Traceback).
"""
import subprocess
import sys
import time
import concurrent.futures

PYTHON = sys.executable
SCRIPTS = [
    "Missing_migrants.py",
    "IOM.py",
    "espagne_frontera_sur.py",
    "Bosnie.py",
    "Bulgarie.py",
    "Italie_CPR.py",
    "Pologne.py",
    "Migrant_files.py",
    "southern_EU.py",
    "fortress_europe.py",
]

SUMMARY_KEYWORDS = (
    "created", "processed", "complete", "other typed",
    "error", "traceback", "warning: could not",
)

TIMEOUT = 15  # secondes

print(f"{'Script':<30} {'Durée':>7}  Résultat")
print("-" * 80)

def run_one(script):
    t0 = time.time()
    try:
        result = subprocess.run(
            [PYTHON, script],
            capture_output=True,
            text=True,
            timeout=TIMEOUT,
            encoding="utf-8",
            errors="replace",
        )
        elapsed = time.time() - t0
        output = result.stdout + result.stderr
        lines = output.splitlines()
        summary = [l.strip() for l in lines if any(kw in l.lower() for kw in SUMMARY_KEYWORDS)]
        if result.returncode != 0:
            status = "ERREUR"
            relevant = [l for l in summary if "error" in l.lower() or "traceback" in l.lower()]
            summary_str = relevant[-1] if relevant else (summary[-1] if summary else lines[-1] if lines else "?")
        else:
            status = "OK"
            summary_str = " | ".join(summary[-4:]) if summary else "(pas de résumé)"
        return script, elapsed, status, summary_str[:110]
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        return script, elapsed, "TIMEOUT", f">{TIMEOUT}s — démarrage OK, données volumineuses"

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
    futures = {ex.submit(run_one, s): s for s in SCRIPTS}
    for fut in concurrent.futures.as_completed(futures):
        script, elapsed, status, summary_str = fut.result()
        print(f"{script:<30} {elapsed:>6.1f}s  [{status}] {summary_str}")

print("-" * 80)
print("Smoke test terminé.")
