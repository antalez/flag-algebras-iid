"""Exactly replay saved violations of the missing seven-point (3,5) blocks.

This verifies negative rational quadratic forms, not an SDP upper bound.
"""
import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from math import comb
from pathlib import Path

from sdp7 import np, candidates, global_event_signs


def check(data, states, primal, diagnostic):
    indices = primal['indices']
    weights = [int(w) for w in primal['weight_numerators']]
    if (primal['coefficient'] != data['coefficient'] or len(indices) != len(weights)
            or any(w < 0 for w in weights) or sum(weights) == 0):
        raise ValueError('Invalid primal weights')
    signs = global_event_signs(data, states[indices])
    lookup = {t: i for i, t in enumerate(candidates(7, False, 2))}
    cache = {}

    def codes(vertices):
        if vertices not in cache:
            ids = [lookup[tuple(vertices[i] for i in t)]
                   for t in candidates(len(vertices), False, 2)]
            cache[vertices] = (signs[:, ids] == 1).astype(np.int64) @ (
                1 << np.arange(len(ids), dtype=np.int64))
        return cache[vertices]

    results = []
    for block in diagnostic['blocks']:
        t, f = block['t'], block['f']
        if (t, f) != (3, 5):
            raise ValueError('This replay implements only (3,5)')
        vector = dict(zip(block['flag_codes'], block['vector_integers']))
        if len(vector) != len(block['flag_codes']):
            raise ValueError('Duplicate flag codes')
        marks = list(combinations(range(f), t))
        numerator = 0
        for roots in combinations(range(7), t):
            selected = np.flatnonzero(codes(roots) == block['root_code'])
            rest = tuple(i for i in range(7) if i not in roots)
            for left in combinations(rest, f-t):
                right = tuple(i for i in rest if i not in left)
                a, b = tuple(sorted(roots+left)), tuple(sorted(roots+right))
                ma = marks.index(tuple(a.index(i) for i in roots))
                mb = marks.index(tuple(b.index(i) for i in roots))
                ca, cb = codes(a)*len(marks)+ma, codes(b)*len(marks)+mb
                numerator += sum(weights[int(i)]*vector.get(int(ca[i]), 0)*
                                 vector.get(int(cb[i]), 0) for i in selected)
        norm = comb(7, t)*comb(7-t, f-t)*comb(7-f, f-t)
        value = Q(numerator, norm*sum(weights)*block['vector_denominator']**2)
        if value != Q(block['quadratic_exact']) or value >= 0:
            raise ValueError('Negative quadratic-form certificate failed')
        results.append(dict(root_code=block['root_code'], quadratic_exact=str(value),
                            exact_violation_verified=True))
    return results


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--primal', type=Path, required=True)
    p.add_argument('--diagnostic', type=Path, required=True)
    args = p.parse_args()
    with np.load(args.cover7) as archive:
        states = archive['states']
    result = check(json.loads(args.cover6.read_text()), states,
                   json.loads(args.primal.read_text()), json.loads(args.diagnostic.read_text()))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
