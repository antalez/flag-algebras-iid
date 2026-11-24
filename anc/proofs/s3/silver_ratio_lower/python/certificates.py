"""Exact arithmetic checks for the recursive constructions; no solver needed."""

import argparse
from fractions import Fraction as Q
import json
from math import comb
from pathlib import Path

from recursive import event_polynomial, exact_probability


def multiply(a, b):
    result = [Q(0)] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def bernstein_split(b):
    left, right = [b[0]], [b[-1]]
    while len(b) > 1:
        b = [(a+c)/2 for a, c in zip(b, b[1:])]
        left.append(b[0])
        right.append(b[-1])
    return left, right[::-1]


def ladder_below_half_certificate():
    # H = 1-3t+6t^2-3t^3; G = 2g = 1-3t^2+4t^3-t^4.
    # Positivity of 27 G^2 - 16 H^3 implies g > 2 (H/3)^(3/2).
    h, g2 = list(map(Q, [1, -3, 6, -3])), list(map(Q, [1, 0, -3, 4, -1]))
    gg, hhh = multiply(g2, g2), multiply(multiply(h, h), h)
    a = [27*(gg[i] if i < len(gg) else 0)-16*hhh[i] for i in range(len(hhh))]
    degree = len(a)-1
    b = [sum(a[j]*Q(comb(k, j), comb(degree, j)) for j in range(k+1))
         for k in range(degree+1)]
    leaves = []

    def verify(coefficients, low, high, depth=0):
        if min(coefficients) > 0:
            leaves.append({"interval": [str(low), str(high)],
                           "bernstein_coefficients": [str(v) for v in coefficients]})
            return
        if depth > 20:
            raise AssertionError("Could not certify positivity")
        left, right = bernstein_split(coefficients)
        midpoint = (low+high)/2
        verify(left, low, midpoint, depth+1)
        verify(right, midpoint, high, depth+1)

    verify(b, Q(0), Q(1))
    return {"polynomial_power_coefficients": [str(v) for v in a],
            "positive_bernstein_pieces": leaves,
            "conclusion": "The entire recursive ladder family, including its N=infinity formula, is strictly below 1/2 for every admissible mass vector."}


def boundary_counterexample():
    # A rational instance just above the endpoint, checked by full enumeration.
    # The README proves the same lower bound for EVERY c>1+sqrt(2), using
    # a=1/sqrt(2) and a sufficiently small rho depending on c.
    c, a, rho = Q("2.415"), Q("0.7071"), Q(1, 100000)
    p, q, r = Q(1, 3), Q(1, 2), Q(1, 6)
    base_terms, _ = event_polynomial([Q(0), a, Q(1)], c)
    f = exact_probability(base_terms, [p, q, r])
    support, masses = [Q(0), rho*a, rho, a, Q(1)], [p*p, p*q, p*r, q, r]
    finite_terms, _ = event_polynomial(support, c)
    finite = exact_probability(finite_terms, masses)
    assert f == Q(161, 324)
    assert finite == f*(1+p**4) == Q(6601, 13122)
    assert finite-Q(1, 2) == Q(20, 6561)
    return {"example_c": str(c), "support_exact": list(map(str, support)),
            "masses_exact": list(map(str, masses)), "probability_exact": str(finite),
            "probability": float(finite), "excess_over_half_exact": str(finite-Q(1, 2)),
            "infinite_recursion_probability_exact": str(f/(1-p**4)),
            "general_statement": "For every c>1+sqrt(2), a five-atom law achieves at least 6601/13122>1/2; see the symbolic argument in README.md."}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = {"ladder_below_half": ladder_below_half_certificate(),
              "above_endpoint": boundary_counterexample()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Exact positivity certificate: recursive ladder family < 1/2.")
    print("Exact five-atom example: 6601/13122 =", float(Q(6601, 13122)), "> 1/2.")


if __name__ == "__main__":
    main()
