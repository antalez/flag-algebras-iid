"""Exact lower-law families at multinacci and intermediate ladder thresholds.

These are uniform constructive lower bounds, not proofs of discontinuities.
Mass optimization is local. All reported selected-event bounds are rational.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

from search import optimize, exact_value
from verify_lower_laws import verify_law


def evaluate(coefficients, c):
    value = Q(0)
    for coefficient in reversed(coefficients):
        value = value*c+coefficient
    return value


def multinacci_polynomial(m):
    if m < 1:
        raise ValueError('Require m>=1')
    return [-1]*m+[1]


def intermediate_polynomial(n):
    if n < 0:
        raise ValueError('Require n>=0')
    if n == 0:
        return [-1, -1, 1]
    coefficients = [0]*(n+3)
    coefficients[0], coefficients[-2], coefficients[-1] = -2, -1, 1
    for j in range(1, n):
        coefficients[j] = -1
    return coefficients


LIMIT_POLYNOMIAL = [-1, 1, -2, 1]


def root_bracket(coefficients, bits=128):
    lo, hi = Q(1, 2), Q(2)
    if not evaluate(coefficients, lo) < 0 < evaluate(coefficients, hi):
        raise ValueError('Expected a root bracket')
    for _ in range(bits):
        mid = (lo+hi)/2
        value = evaluate(coefficients, mid)
        if not value:
            return mid, mid
        if value > 0:
            hi = mid
        else:
            lo = mid
    return lo, hi


def multinacci_support(c, m):
    if not 1 < c < 2 or evaluate(multinacci_polynomial(m), c) <= 0:
        raise ValueError('Require a coefficient strictly above the multinacci root and below 2')
    if m == 1:
        return [Q(0), Q(1)]
    r = [sum((c**(-k) for k in range(1, j+2)), Q(0)) for j in range(m-1)]
    scale = (1+(c-1)/r[-1])/2
    return [Q(0)]+[scale*v for v in r]+[Q(1)]


def intermediate_support(c, n):
    if not 1 < c < 2 or evaluate(intermediate_polynomial(n), c) <= 0:
        raise ValueError('Require a coefficient strictly above the intermediate root and below 2')
    r, u = [1/c], [1/c]
    for _ in range(n):
        r.append((r[0]+r[-1])/c)
        u.append((u[0]+u[-1]+1)/c)
    delta = (c-1-r[-1])/(2*u[-1])
    return [Q(0)]+[a+delta*b for a, b in zip(r, u)]+[Q(1)]


def limit_support(c):
    if not 1 < c < 2 or evaluate(LIMIT_POLYNOMIAL, c) <= 0:
        raise ValueError('Require eta<c<2')
    a = (1/c+(c-1)**2)/2
    b = (a/(c-1)+c-1)/2
    return [Q(0), a, b, Q(1)]



def family_definition(kind, index):
    if kind == 'multinacci':
        return multinacci_polynomial(index), lambda c: multinacci_support(c, index)
    if kind == 'intermediate':
        return intermediate_polynomial(index), lambda c: intermediate_support(c, index)
    if kind == 'limit' and index is None:
        return LIMIT_POLYNOMIAL, limit_support
    raise ValueError('Unknown family or index')


def selected_success(kind, i, j, k, top):
    if kind == 'multinacci':
        return min(i, j) < k
    if k > 0 and (i == 0 or j == 0):
        return True
    if k == top and min(i, j) < top:
        return True
    if kind == 'intermediate':
        return 0 < k < top and min(i, j) == 1 and max(i, j) < k
    if kind == 'limit':
        return k == 2 and min(i, j) == 1 and max(i, j) <= 2
    raise ValueError('Unknown family')


def selected_terms(kind, size):
    terms = Counter()
    for i, j, k in product(range(size), repeat=3):
        if selected_success(kind, i, j, k, size-1):
            terms[tuple((i, j, k).count(v) for v in range(size))] += 1
    return terms


def generate(kind, index, starts):
    polynomial, support = family_definition(kind, index)
    lo, hi = root_bracket(polynomial)
    c = Q(int((lo+hi)/2*10**12), 10**12)+Q('0.00001')
    xs = support(c)
    terms = selected_terms(kind, len(xs))
    law = optimize(xs, c, starts=starts)
    checked = verify_law(c, law)
    for i, j, k in product(range(len(xs)), repeat=3):
        if selected_success(kind, i, j, k, len(xs)-1) and not xs[i]+xs[j] < c*xs[k]:
            raise ValueError('A selected event is not a strict success')
    masses = list(map(Q, law['masses_exact']))
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    if value > Q(checked['exact_lower']):
        raise ValueError('Selected-event lower exceeds full base counting')
    return dict(family=kind, index=index, polynomial=polynomial,
                root_bracket=list(map(str, (lo, hi))), root_approx=float((lo+hi)/2),
                c=str(c), selected_ordered_successes=sum(terms.values()),
                selected_base_exact=str(f), uniform_right_lower_exact=str(value),
                uniform_right_lower=float(value), sampled_law=law, sampled_verification=checked,
                interpretation='Uniform right-side constructive lower; no discontinuity or optimality claim')



def verify_uniform_family(row):
    """Check fixed masses and the selected-event lower from the analytic family.

    The support formulas prove every selected success for root<c<2;
    see MULTINACCI.md for the recurrence and positive-slack identities.
    Numerical root approximations and optimization objectives are not used.
    """
    kind, index = row['family'], row['index']
    polynomial, support = family_definition(kind, index)
    if row['polynomial'] != polynomial:
        raise ValueError('Lower-family polynomial mismatch')
    c = Q(row['c'])
    if not 1 < c < 2 or evaluate(polynomial, c) <= 0:
        raise ValueError('Lower witness is not on the requested right side')
    law = row['sampled_law']
    verify_law(c, law)
    xs = support(c)
    if list(map(Q, law['support_exact'])) != xs:
        raise ValueError('Saved support does not match the analytic family')
    masses = list(map(Q, law['masses_exact']))
    if len(masses) != len(xs) or min(masses) < 0 or sum(masses) != 1 or masses[0] == 1:
        raise ValueError('Invalid family masses')
    terms = selected_terms(kind, len(xs))
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    if value != Q(row['uniform_right_lower_exact']) or f != Q(row['selected_base_exact']):
        raise ValueError('Incorrect uniform selected-event bound')
    return dict(statement='S2(c) >= value_exact for every c strictly above the indicated root',
                family=kind, index=index, polynomial=polynomial,
                selected_ordered_successes=sum(terms.values()), masses_exact=list(map(str, masses)),
                base_exact=str(f), value_exact=str(value), decimal=float(value), exact_checked=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--multinacci', type=int, nargs='+', default=[1, 2, 3, 4])
    p.add_argument('--intermediate', type=int, nargs='+', default=[1, 2, 3, 4, 5, 6])
    p.add_argument('--starts', type=int, default=12)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.starts < 1:
        p.error('Require at least one start')
    rows = []
    for kind, indices in [('multinacci', args.multinacci), ('intermediate', args.intermediate), ('limit', [None])]:
        for index in indices:
            row = generate(kind, index, args.starts)
            rows.append(row)
            print(json.dumps({k: row[k] for k in ['family', 'index', 'root_approx', 'uniform_right_lower']}), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
