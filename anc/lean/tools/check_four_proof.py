"""Compile and audit the direct four-point equality theorem.

First run check_four.py. Shared mathematical lemmas and the existing lower
construction are reused; missing dependencies and new bridge modules are
compiled directly, without loading optional native libraries.
"""
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not (ROOT / "Fast/Cert8Data.lean").is_file():
        raise SystemExit("Restore the original LFS archive first; shared field and "
                         "matrix lemmas import its definitions. See anc/lean/README.md.")
    if not (ROOT / ".lake/build/lib/lean/Fast/Four/Checked.olean").is_file():
        raise SystemExit("Run python3 anc/lean/tools/check_four.py first.")
    # Direct compilation avoids mixing Lake native-library artifacts with the
    # kernel-only runner's manually compiled oleans. External Mathlib oleans
    # still come from the pinned Lake environment.
    seen = set()
    shared = []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            return
        for dep in re.findall(r"^import ([\w.]+)$", source.read_text(), re.M):
            visit(dep)
        shared.append(module)

    for module in ["BeatAvg.Five.Matrix", "BeatAvg.Five.Cover",
                   "BeatAvg.Cert.SortedN", "BeatAvg.Lower.Main"]:
        visit(module)
    new_modules = ["Fast.Four.Objective"] + [
        "BeatAvg.Four." + name for name in
        ["Config", "Flag", "FlagExpectation", "FlagPermutation", "Generic",
         "Cover", "SamplePattern", "BitSpecs", "PatternConfig", "Matrix",
         "Families", "Arrangements", "Functional", "Evaluation", "Final"]]
    report = []
    logs = ROOT / ".lake/four-proof-logs"
    logs.mkdir(exist_ok=True)
    for module in shared + new_modules:
        source = ROOT / (module.replace(".", "/") + ".lean")
        output = ROOT / (".lake/build/lib/lean/" + module.replace(".", "/") + ".olean")
        if module in shared and output.is_file():
            deps = re.findall(r"^import ([\w.]+)$", source.read_text(), re.M)
            local_deps = [ROOT / (".lake/build/lib/lean/" + dep.replace(".", "/") + ".olean")
                          for dep in deps
                          if (ROOT / (dep.replace(".", "/") + ".lean")).is_file()]
            newest = max([source.stat().st_mtime] +
                         [dep.stat().st_mtime for dep in local_deps])
            if output.stat().st_mtime >= newest:
                continue
        output.parent.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        result = subprocess.run(
            ["/usr/bin/time", "-f", "peak_rss_kb=%M", lake, "env", "lean",
             "-DautoImplicit=false", "-o", str(output), str(source)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (module + ".log")).write_text(result.stdout)
        rss = re.search(r"peak_rss_kb=(\d+)", result.stdout)
        report.append(dict(module=module, seconds=round(time.monotonic()-started, 3),
                           peak_rss_kb=int(rss[1]) if rss else None,
                           returncode=result.returncode))
        (ROOT / ".lake/four-proof-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{module}: {report[-1]['seconds']}s, exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise SystemExit(result.returncode)
    audit = subprocess.run([lake, "env", "lean", "-DautoImplicit=false", "CheckFour.lean"],
                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / ".lake/four-axiom-audit.txt").write_text(audit.stdout)
    print(audit.stdout, end="", flush=True)
    if audit.returncode:
        raise SystemExit(audit.returncode)
    for line in audit.stdout.splitlines():
        if "depends on axioms:" in line:
            listed = line.split("depends on axioms:", 1)[1].strip().strip("[]")
            if set(a.strip() for a in listed.split(",") if a.strip()) - {
                    "propext", "Classical.choice", "Quot.sound"}:
                raise SystemExit("Unexpected axiom: " + line)
    if "'BeatAvg.Four.C_eq_Bstar' depends on axioms:" not in audit.stdout:
        raise SystemExit("Final equality axiom audit missing.")
    print("Direct four-point C = Bstar proved; axiom audit passed.", flush=True)


if __name__ == "__main__":
    main()
