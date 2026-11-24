"""Independently count saved recursive iid lower laws with rational arithmetic."""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def verify_law(c, saved):
    xs = list(map(Q, saved['support_exact']))
    ps = list(map(Q, saved['masses_exact']))
    if (len(xs) != len(ps) or len(xs) < 2 or xs[0] != 0 or xs[-1] != 1
            or any(a >= b for a, b in zip(xs, xs[1:]))
            or any(p < 0 for p in ps) or sum(ps) != 1 or ps[0] == 1):
        raise ValueError('Invalid normalized recursive base law')
    successes = [(i, j, k) for i, j, k in product(range(len(xs)), repeat=3)
                 if xs[i]+xs[j] < c*xs[k]]
    f = sum((ps[i]*ps[j]*ps[k] for i, j, k in successes), Q(0))
    slack = min(c*xs[k]-xs[i]-xs[j] for i, j, k in successes)
    rho = Q(saved.get('rho_exact', saved.get('recursive_scale_exact')))
    base = Q(saved.get('base_exact', saved.get('base_probability_exact')))
    value = Q(saved.get('value_exact', saved.get('recursive_lower_bound_exact')))
    if not (0 < rho < xs[1] and 2*rho < slack and c*rho < xs[1]):
        raise ValueError('Zero replacement does not preserve counted successes')
    if f != base or f/(1-ps[0]**3) != value:
        raise ValueError('Claimed exact lower probability does not match counting')
    claimed_slack = saved.get('slack_exact', saved.get('minimum_success_slack_exact'))
    if claimed_slack is not None and slack != Q(claimed_slack):
        raise ValueError('Claimed minimum success slack is incorrect')
    return dict(exact_lower=str(value), lower=float(value), base_exact=str(f),
                slack_exact=str(slack), exact_checked=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('witnesses', nargs='+', type=Path)
    args = p.parse_args()
    results = []
    for path in args.witnesses:
        data = json.loads(path.read_text())
        c = Q(data['c'])
        laws = data['laws'] if 'laws' in data else [data]
        results.append(dict(source=str(path), c=str(c), laws=[verify_law(c, law) for law in laws]))
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
