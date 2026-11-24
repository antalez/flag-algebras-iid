"""Kernel-check the direct four-point certificate in bounded compiler processes.

No native_decide. Shared Fast definitions are compiled directly first;
all new finite modules are independent of Mathlib.
Reports and individual logs go to the ignored .lake directory.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/build/lib/lean"
REPORT = ROOT / ".lake/four-check-report.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    assert args.jobs > 0
    dependencies = ["Fast.K", "Fast.Pat", "Fast.Gen", "Fast.Canon",
                    "Fast.Five.Basic", "Fast.Five.Check", "Fast.Five.Config"]
    lean = subprocess.check_output(
        [shutil.which("elan") or str(Path.home() / ".elan/bin/elan"), "which", "lean"],
        cwd=ROOT, text=True).strip()
    env = dict(os.environ, LEAN_PATH=str(OUT))
    imports = re.findall(r"^import (Fast.Four.Checks.\w+)$",
                         (ROOT / "Fast/Four/Checked.lean").read_text(), re.M)
    shared = ["Fast.Four.Basic", "Fast.Four.Data"]
    seen = set()

    def import_sources(module):
        if module in seen:
            return b""
        seen.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            return b""
        data = source.read_bytes()
        imported = re.findall(r"^import ([\w.]+)$", data.decode(), re.M)
        return module.encode() + data + b"".join(import_sources(m) for m in imported)

    digest = hashlib.sha256(b"".join(import_sources(m) for m in shared)).hexdigest()
    prior = json.loads(REPORT.read_text()) if args.resume and REPORT.exists() else []
    cache = {r["module"]: r for r in prior}
    records = []
    logs = ROOT / ".lake/four-logs"
    logs.mkdir(exist_ok=True)

    def build(module):
        source = ROOT / (module.replace(".", "/") + ".lean")
        output = OUT / (module.replace(".", "/") + ".olean")
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        previous = cache.get(module)
        if (args.resume and output.exists() and previous and previous["returncode"] == 0
                and previous.get("shared_hash") == digest
                and previous.get("source_hash") == source_hash):
            return previous
        output.parent.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        result = subprocess.run(
            ["/usr/bin/time", "-f", "peak_rss_kb=%M", lean, "-DautoImplicit=false",
             "-o", str(output), str(source)], cwd=ROOT, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (module + ".log")).write_text(result.stdout)
        rss = re.search(r"peak_rss_kb=(\d+)", result.stdout)
        record = dict(module=module, seconds=round(time.monotonic()-started, 3),
                      peak_rss_kb=int(rss[1]) if rss else None,
                      returncode=result.returncode, shared_hash=digest,
                      source_hash=source_hash)
        print(f"{module}: {record['seconds']}s, {record['peak_rss_kb']} KB, "
              f"exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
        return record

    def save(record):
        records.append(record)
        REPORT.write_text(json.dumps(records, indent=2) + "\n")
        if record["returncode"]:
            raise SystemExit(record["returncode"])

    for module in dependencies + shared:
        save(build(module))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for record in pool.map(build, imports):
            save(record)
    save(build("Fast.Four.Checked"))
    print("All four-point finite checks proved by the Lean kernel.", flush=True)


if __name__ == "__main__":
    main()
