#!/usr/bin/env python3
import subprocess
import sys
import time
from pathlib import Path

SCRIPTS = [
    "Allemagne.py",
    "southern_EU.py",
    "IOM.py",
    "fortress_europe.py",
    "Pologne.py",
    "Migrant_files.py",
    "Missing_migrants.py",
    "espagne_frontera_sur.py",
    "Italie_CPR.py",
    "Bosnie.py",
    "Bulgarie.py",
]

root = Path(__file__).resolve().parent
logs_dir = root / "run_logs"
logs_dir.mkdir(exist_ok=True)

python_exe = sys.executable

print(f"Python: {python_exe}")
print(f"Workspace: {root}")
print("=" * 90)

overall_t0 = time.perf_counter()
results = []

for script in SCRIPTS:
    script_path = root / script
    log_path = logs_dir / f"{script_path.stem}.log"

    if not script_path.exists():
        print(f"[MISSING] {script}")
        results.append((script, "MISSING", 0.0))
        continue

    print(f"[START] {script}")
    t0 = time.perf_counter()

    with log_path.open("w", encoding="utf-8", errors="replace") as logf:
        logf.write(f"Running {script}\n")
        logf.write("=" * 60 + "\n")
        try:
            proc = subprocess.run(
                [python_exe, str(script_path)],
                cwd=str(root),
                stdout=logf,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=300,
            )
            returncode = proc.returncode
        except subprocess.TimeoutExpired:
            logf.write("\n[TIMEOUT] Script killed after 300s\n")
            returncode = -9

    elapsed = time.perf_counter() - t0
    status = "TIMEOUT" if returncode == -9 else ("OK" if returncode == 0 else f"ERR({returncode})")
    print(f"[DONE]  {script:<24} {status:<8} {elapsed:8.1f}s  log={log_path.name}")
    results.append((script, status, elapsed))

print("=" * 90)
overall_elapsed = time.perf_counter() - overall_t0
print(f"Total elapsed: {overall_elapsed:.1f}s")

for script, status, elapsed in results:
    print(f" - {script:<24} {status:<8} {elapsed:8.1f}s")
