"""Remove globally impossible seven-point rows using exact Farkas proofs.

Writes a copy of the six-point cover with additional seven_exclusions.
All existing solvers recheck these proofs when rebuilding its seven-cover.
Numerical infeasibility alone never excludes a row. Reruns resume proofs.
"""
import argparse
import json
from pathlib import Path
import time

from sdp7 import (np, candidates, gap_rows, Q2, enumerate_seven,
                  global_event_signs, verify_seven_exclusions, save)
from enumerate_patterns import certificate
import highspy


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seconds', type=float, default=600)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    if args.output.exists():
        prior = json.loads(args.output.read_text())
        if (prior['coefficient'] != data['coefficient'] or prior['patterns'] != data['patterns']
                or prior['tuples'] != data['tuples'] or prior['pruned'] != data['pruned']):
            raise ValueError('Incompatible resume cover')
        data['seven_exclusions'] = prior.get('seven_exclusions', {})
    verify_seven_exclusions(data)
    states, _, _, meta = enumerate_seven(data)
    if not meta['complete']:
        raise ValueError('Incomplete compatible cover')
    signs = global_event_signs(data, states)
    rows = gap_rows(7, candidates(7, False, 2), Q2(*data['coefficient']))
    a = np.array([[float(v) for v in row] for row in rows])
    h = highspy.Highs()
    for key, value in [('output_flag', False), ('solver', 'simplex'),
                       ('presolve', 'off'), ('primal_feasibility_tolerance', 1e-9),
                       ('dual_feasibility_tolerance', 1e-9)]:
        h.setOptionValue(key, value)
    h.addCols(7, np.ones(7), np.zeros(7), np.full(7, highspy.kHighsInf),
              0, np.zeros(8, dtype=np.int32), np.array([], dtype=np.int32), np.array([]))
    n = len(rows)
    h.addRows(n, np.full(n, -highspy.kHighsInf), np.full(n, highspy.kHighsInf),
              n*7, np.arange(0, (n+1)*7, 7, dtype=np.int32),
              np.tile(np.arange(7, dtype=np.int32), n), a.ravel())
    excluded = data.setdefault('seven_exclusions', {})
    tick = last = time.monotonic()
    unverified = checked = 0
    for checked, pattern in enumerate(signs, 1):
        h.changeRowsBounds(n, np.arange(n, dtype=np.int32),
                           np.where(pattern == 1, -highspy.kHighsInf, 1.),
                           np.where(pattern == 1, -1., highspy.kHighsInf))
        if h.run() == highspy.HighsStatus.kError:
            raise RuntimeError('HiGHS failed to run the global realization LP')
        if h.getModelStatus() == highspy.HighsModelStatus.kInfeasible:
            _, exists, ray = h.getDualRay()
            proof = certificate(rows, pattern, -np.array(ray)*pattern) if exists else None
            if proof is not None:
                key = ''.join('+' if v == 1 else '-' for v in pattern)
                excluded[key] = proof
            else:
                unverified += 1
        now = time.monotonic()
        if now-last > 20 or checked == len(signs) or now-tick > args.seconds:
            data['seven_filter'] = dict(checked=checked, input_rows=len(signs),
                exact_exclusions=len(excluded), unverified_rays=unverified,
                complete_pass=checked == len(signs), seconds=now-tick)
            save(args.output, data)
            print(json.dumps(data['seven_filter']), flush=True)
            last = now
        if now-tick > args.seconds:
            break
    verify_seven_exclusions(data)


if __name__ == '__main__':
    main()
