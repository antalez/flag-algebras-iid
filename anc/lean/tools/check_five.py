"""Kernel-check the five-point certificate in sequential, memory-bounded batches.

Run from any directory: python3 anc/lean/tools/check_five.py
Requires the pinned Lean toolchain. Uses only Lean's kernel (`decide +kernel`),
not native_decide. This checks finite certificate identities, not yet C = Bstar.
Each module gets a separate compiler process; no eight-point data is imported.
Timing and peak RSS are saved to .lake/five-check-report.json (not versioned).
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'
REPORT = ROOT / '.lake/five-check-report.json'


def main():
    lean = subprocess.check_output(
        [shutil.which('elan') or str(Path.home() / '.elan/bin/elan'), 'which', 'lean'], cwd=ROOT, text=True
    ).strip()
    env = dict(os.environ, LEAN_PATH=str(OUT))
    imports = re.findall(r'^import (Fast.Five.Checks.\w+)$',
                         (ROOT / 'Fast/Five/Checked.lean').read_text(), re.M)
    modules = ['Fast.K', 'Fast.Five.Basic', 'Fast.Five.Check', 'Fast.Five.Data']
    modules += imports + ['Fast.Five.Checked']
    records = []
    for index, module in enumerate(modules):
        source = ROOT / (module.replace('.', '/') + '.lean')
        output = OUT / (module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = ROOT / '.lake' / 'five-check-current.log'
        started = time.monotonic()
        result = subprocess.run(['/usr/bin/time', '-f', 'peak_rss_kb=%M',
                                 lean, '-o', str(output), str(source)],
                                cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - started
        log.write_text(result.stdout)
        rss = re.search(r'peak_rss_kb=(\d+)', result.stdout)
        records.append(dict(module=module, seconds=round(elapsed, 3),
                            peak_rss_kb=int(rss[1]) if rss else None,
                            returncode=result.returncode))
        REPORT.write_text(json.dumps(records, indent=2) + '\n')
        print(f'[{index+1}/{len(modules)}] {module}: '
              f'{elapsed:.2f}s, {records[-1]["peak_rss_kb"]} KB', flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise SystemExit(result.returncode)
    print(f'Total compiler time: {sum(r["seconds"] for r in records):.2f}s; '
          f'peak RSS: {max(r["peak_rss_kb"] or 0 for r in records)} KB')
    print('All finite checks kernel-verified. Full probability bridge is still pending.')


if __name__ == '__main__':
    main()
