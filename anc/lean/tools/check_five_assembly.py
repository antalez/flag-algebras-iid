"""Generate and kernel-check the finite identities connecting the sample functional
with the original certificate scores. No native_decide or Mathlib is needed.
Use --jobs 2 to check two patterns concurrently (about 1.3 GB per worker).
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    cover = ROOT.parent / 'proofs/s3/0.400695372__c2/five_point/n5_cut2_exact_cover.json'
    count = len(json.loads(cover.read_text())['patterns'])
    dest = ROOT / 'Fast/Five/AssemblyChecks'
    dest.mkdir(exist_ok=True)
    header = 'import Fast.Five.AssembledCheck\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\nnamespace Fast.Five.AssemblyChecked\n'
    modules = []
    for i in range(count):
        module = f'Fast.Five.AssemblyChecks.Pattern{i:03d}'
        modules.append(module)
        (ROOT / (module.replace('.', '/') + '.lean')).write_text(header +
            f'theorem pattern{i} : assembledOk Data.patterns[{i}]! = true := by decide +kernel\n' +
            'end Fast.Five.AssemblyChecked\n')
    expr = 'true'
    for i in reversed(range(count)):
        expr = f'(assembledOk Data.patterns[{i}]! && {expr})'
    (ROOT / 'Fast/Five/AssemblyChecked.lean').write_text('\n'.join('import ' + m for m in modules) +
        '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\nnamespace Fast.Five.AssemblyChecked\n' +
        'theorem all : Data.patterns.toList.all assembledOk = true := by\n' +
        f'  change {expr} = true\n  simp only [' + ', '.join(f'pattern{i}' for i in range(count)) +
        ', Bool.true_and]\nend Fast.Five.AssemblyChecked\n')
    lean = subprocess.check_output([shutil.which('elan') or str(Path.home()/'.elan/bin/elan'),
                                    'which', 'lean'], cwd=ROOT, text=True).strip()
    env = dict(os.environ, LEAN_PATH=str(OUT))
    report = []
    def compile_module(module):
        source = ROOT / (module.replace('.', '/')+'.lean')
        output = OUT / (module.replace('.', '/')+'.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        proc = subprocess.run(['/usr/bin/time', '-f', 'peak_rss_kb=%M', lean,
                               '-o', str(output), str(source)], cwd=ROOT, env=env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic()-start
        rss = re.search(r'peak_rss_kb=(\d+)', proc.stdout)
        return dict(module=module, seconds=round(elapsed,3), returncode=proc.returncode,
                    peak_rss_kb=int(rss[1]) if rss else None), proc.stdout
    def record(result):
        row, log = result
        report.append(row)
        (ROOT/'.lake/five-assembly-report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(f'{row["module"]}: {row["seconds"]}s, {row["peak_rss_kb"]} KB, exit {row["returncode"]}',flush=True)
        if row['returncode']:
            print(log,flush=True)
            return False
        return True
    base = ['Fast.K','Fast.Pat','Fast.Gen','Fast.Canon','Fast.Five.Basic','Fast.Five.Check',
            'Fast.Five.Data','Fast.Five.Config','Fast.Five.FlagCodes','Fast.Five.PatternConfig',
            'Fast.Five.Arrangements','Fast.Five.AssembledCheck']
    for module in base:
        if not record(compile_module(module)):
            raise SystemExit(1)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(compile_module,module) for module in modules]
        for future in as_completed(futures):
            if not record(future.result()):
                for pending in futures:
                    pending.cancel()
                raise SystemExit(1)
    if not record(compile_module('Fast.Five.AssemblyChecked')):
        raise SystemExit(1)
    print('All sample-to-certificate identities are kernel-verified.',flush=True)

if __name__ == '__main__':
    main()
