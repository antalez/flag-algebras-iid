"""Compile and audit the complete five-point probability proof.

First run check_five.py and check_five_assembly.py. This script deliberately
builds the new mathematical modules directly, so Lake does not launch hundreds
of finite kernel checks concurrently. Existing mathematical lemmas and the
lower construction are built normally by Lake. See anc/lean/README.md for LFS and
Mathlib setup on a fresh clone.
"""
import json
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    lake = shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
    if not (ROOT/'Fast/Cert8Data.lean').is_file():
        raise SystemExit('The reused mathematical modules need the original payload. '
                         'Run git lfs pull, then python3 anc/lean/tools/restore_artifacts.py '
                         'anc/lean/artifacts/beat_the_average_kernel.zip from the repository root.')
    for name in ['Fast/Five/Checked.olean', 'Fast/Five/AssemblyChecked.olean']:
        if not (ROOT/'.lake/build/lib/lean'/name).is_file():
            raise SystemExit('Missing '+name+'; run check_five.py and check_five_assembly.py first.')
    subprocess.run([lake, 'build', 'BeatAvg.Cert.SortedN', 'BeatAvg.Cert.DegTerm',
                    'BeatAvg.Cert.QPsd', 'BeatAvg.ExpectDeg', 'BeatAvg.Atomless',
                    'BeatAvg.Lower.Main'], cwd=ROOT, check=True)
    names = ['Config', 'Flag', 'FlagExpectation', 'Generic', 'Gordan',
             'Field', 'Endpoints', 'Probability', 'ScalarExpectation', 'Matrix',
             'Matrices', 'Cover', 'SamplePattern', 'BitSpecs', 'PatternConfig',
             'Families', 'FlagPermutation', 'Arrangements', 'Sample', 'Functional',
             'ColorFacts', 'ScalarEvaluation', 'SquareEvaluation', 'Evaluation',
             'FinalCore', 'Final']
    report = []
    for name in names:
        output = ROOT/f'.lake/build/lib/lean/BeatAvg/Five/{name}.olean'
        output.parent.mkdir(parents=True,exist_ok=True)
        started = time.monotonic()
        result = subprocess.run([lake, 'env', 'lean', '-DautoImplicit=false',
                                 '-o', str(output), f'BeatAvg/Five/{name}.lean'], cwd=ROOT)
        report.append(dict(module='BeatAvg.Five.'+name, seconds=round(time.monotonic()-started,3),
                           returncode=result.returncode))
        (ROOT/'.lake/five-proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
        if result.returncode:
            raise SystemExit(result.returncode)
        print('Built BeatAvg.Five.'+name,flush=True)
    subprocess.run([lake, 'env', 'lean', '-DautoImplicit=false', 'CheckFive.lean'],cwd=ROOT,check=True)
    print('C = Bstar proved using the five-point colored certificate; axiom audit above.')

if __name__ == '__main__':
    main()
