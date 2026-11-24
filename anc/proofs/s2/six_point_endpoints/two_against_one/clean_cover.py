"""Remove infeasible six-point leaves only after exact rational Farkas checks.

The binary cover remains complete: each removed full leaf is replaced by
an exactly certified pruned branch. Numerical LP decisions alone never prune.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

import highspy
from sdp6 import np, verify_cover, save
from sdp7 import gap_rows, candidates, Q2
from enumerate_patterns import certificate
from endpoint_c4 import reconstruct_with_alternatives


def clean(data):
    verify_cover(data)
    if data['size'] != 6 or data.get('summands') != 2 or data['coefficient'][1] != '0':
        raise ValueError('Expected a rational two-summand six-point cover')
    c = Q(data['coefficient'][0])
    rows = gap_rows(6, candidates(6, False, 2), Q2(c))
    a = np.array([[float(v) for v in row] for row in rows])
    m = len(rows)
    h = highspy.Highs()
    for key, value in [('output_flag', False), ('solver', 'simplex'), ('presolve', 'off'),
                       ('primal_feasibility_tolerance', 1e-9), ('dual_feasibility_tolerance', 1e-9)]:
        h.setOptionValue(key, value)
    h.addCols(6, np.ones(6), np.zeros(6), np.full(6, highspy.kHighsInf), 0,
              np.zeros(7, dtype=np.int32), np.array([], dtype=np.int32), np.array([]))
    h.addRows(m, np.full(m, -highspy.kHighsInf), np.full(m, highspy.kHighsInf), m*6,
              np.arange(0, (m+1)*6, 6, dtype=np.int32),
              np.tile(np.arange(6, dtype=np.int32), m), a.ravel())
    kept, removed, unresolved = [], 0, 0
    for pattern in data['patterns']:
        signs = np.array([1 if v == '+' else -1 for v in pattern])
        h.changeRowsBounds(m, np.arange(m, dtype=np.int32),
                          np.where(signs == 1, -highspy.kHighsInf, 1.),
                          np.where(signs == 1, -1., highspy.kHighsInf))
        if h.run() == highspy.HighsStatus.kError:
            raise RuntimeError('HiGHS failed to run')
        proof = None
        if h.getModelStatus() == highspy.HighsModelStatus.kInfeasible:
            _, exists, dual = h.getDualRay()
            if exists:
                ray = -np.asarray(dual)*signs
                proof = certificate(rows, signs, ray)
                if proof is None and max(abs(ray)):
                    scale = max(abs(ray))
                    seed = {str(i): [str(Q(float(w/scale)).limit_denominator(10**6)), '0']
                            for i, w in enumerate(ray) if w > scale*1e-10}
                    try:
                        # Degree-one reduction evaluates polynomials exactly at c.
                        exact = reconstruct_with_alternatives(6, pattern, seed, c,
                            (c.numerator, c.numerator, c.denominator), polynomial=[-c, 1])
                        weights = [sum(Q(v)*c**j for j, v in enumerate(p)) for p in exact['weights']]
                        proof = {str(i): [str(w), '0'] for i, w in zip(exact['events'], weights) if w}
                    except (ValueError, TypeError):
                        pass
            if proof is None:
                unresolved += 1
        if proof is None:
            kept.append(pattern)
        else:
            # Check rational signs independently before modifying the cover.
            weights = {int(i): Q(v[0]) for i, v in proof.items()}
            if (not weights or min(weights.values()) < 0 or max(weights.values()) <= 0
                    or any(sum((Q2(w)*int(signs[i])*rows[i][j] for i, w in weights.items()), Q2()).sign() < 0
                           for j in range(6))):
                raise ValueError('Invalid rational cleanup proof')
            data['pruned'][pattern] = proof
            removed += 1
    original = len(data['patterns'])
    data['patterns'] = kept
    data['leaf_cleanup'] = dict(input_rows=original, removed=removed, remaining=len(kept),
                                unverified_infeasibilities=unresolved)
    verify_cover(data)
    return data


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    data = clean(json.loads(args.cover.read_text()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    save(args.output, data)
    print(json.dumps(data['leaf_cleanup']), flush=True)


if __name__ == '__main__':
    main()
