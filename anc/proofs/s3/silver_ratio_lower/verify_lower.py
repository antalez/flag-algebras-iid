"""Exact endpoint ladder enumeration and rational witness checks; standard library."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[0], -x[1]


def mul(x, y):
    return x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0]


def positive(x):
    """Sign of a+b*sqrt(2), using rational comparisons and squaring only."""
    a, b = x
    if a >= 0 and b >= 0:
        return a > 0 or b > 0
    if a <= 0 and b <= 0:
        return False
    return a*a > 2*b*b if a > 0 else 2*b*b > a*a


def numerator(p, q, r, n):
    return (p**3*(q+r) + 3*p*p*(q+r)**2
            + 3*p*(q**3+3*q*q*r+2*q*r*r+r**3)
            + q**3*r + Q(3, 2)*q*q*r*r*Q(n-1, n))


def endpoint(n):
    zero, one, c = (Q(0), Q(0)), (Q(1), Q(0)), (Q(1), Q(1))
    support = [zero, one] + [(Q(1, 4**j), 1-Q(1, 4**j))
                             for j in range(1, n+1)]
    # Coefficients of p^i q^j r^k, after assigning mass r/n to each tail.
    counts = Counter()
    minimum = None
    for indices in product(range(n+2), repeat=4):
        lhs = zero
        for i in indices[:3]:
            lhs = add(lhs, support[i])
        slack = add(mul(c, support[indices[3]]), neg(lhs))
        if positive(slack):
            exponents = (indices.count(0), indices.count(1),
                         sum(i >= 2 for i in indices))
            counts[exponents] += Q(1, n**exponents[2])
            if minimum is None or positive(add(minimum, neg(slack))):
                minimum = slack
    expected = {(3, 1, 0): Q(1), (3, 0, 1): Q(1),
                (2, 2, 0): Q(3), (2, 1, 1): Q(6), (2, 0, 2): Q(3),
                (1, 3, 0): Q(3), (1, 2, 1): Q(9),
                (1, 1, 2): Q(6), (1, 0, 3): Q(3),
                (0, 3, 1): Q(1), (0, 2, 2): Q(3, 2)*Q(n-1, n)}
    assert counts == Counter({e: v for e, v in expected.items() if v})
    assert minimum is not None and positive(minimum)
    # Select a rational scale below the note's bounds without approximating sqrt(2).
    rho = Q(1, 2)
    maximum = support[-1]
    while (not positive(add(minimum, neg(mul((6*rho, Q(0)), maximum))))
           or not positive(add(one, neg(mul((2*rho, Q(0)), mul(c, maximum)))))):
        rho /= 2
    print(f"endpoint N={n}: exact polynomial; minimum margin={minimum}; safe rho={rho}")


def rational_witness(case):
    c, rho = Q(case['c']), Q(case['safe_scale_ratio_exact'])
    support = list(map(Q, case['support_exact']))
    masses = list(map(Q, case['masses_exact']))
    assert 2 < c < 3 and (c-1)**2 < 2
    assert len(support) == len(masses) and support == sorted(set(support))
    assert support[0] == 0 and support[-1] == 1
    assert min(masses) >= 0 and sum(masses) == 1 and masses[0] < 1
    probability, minimum = Q(0), None
    for indices in product(range(len(support)), repeat=4):
        slack = c*support[indices[3]] - sum(support[i] for i in indices[:3])
        if slack > 0:
            weight = Q(1)
            for i in indices:
                weight *= masses[i]
            probability += weight
            minimum = slack if minimum is None else min(minimum, slack)
    assert minimum is not None and 0 < rho < support[1]
    assert 3*rho < minimum and c*rho < support[1]
    p, q = masses[:2]
    n, r = case['tail_atoms'], sum(masses[2:])
    assert masses[2:] == [r/n]*n
    assert probability == numerator(p, q, r, n)
    assert probability/(1-p**4) == Q(case['recursive_probability_exact'])
    if 'threshold_bracket' in case:
        lo, hi = map(Q, case['threshold_bracket'])
        assert hi == c and 0 < hi-lo <= Q(1, 10**9)
        for coefficient, expected in ((lo, False), (hi, True)):
            atom = Q(1)
            for _ in range(n):
                atom = (2+atom)/coefficient
            assert (atom < coefficient-1) == expected


def main():
    for n in (1, 3, 4, 5):
        endpoint(n)
    count = 0
    for filename in ('lower_ladders.json', 'lower_thresholds.json'):
        for case in json.loads((HERE/'witnesses'/filename).read_text())['cases']:
            rational_witness(case)
            count += 1
    print(f"{count} rational witnesses: probabilities, scales, and threshold brackets verified")


if __name__ == '__main__':
    main()
