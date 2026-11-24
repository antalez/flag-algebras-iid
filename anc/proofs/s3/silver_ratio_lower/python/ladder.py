"""Generalized upper block: a0=1, a(j+1)=(2+a(j))/c, then recurse at zero.

Strictly feasible blocks are constructed with a rational perturbation.
N is the number of small-mass tail atoms after the large atom a0.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, minimize

from recursive import event_polynomial, exact_probability


def block(c, n):
    a = Fraction(1)
    for _ in range(n):
        a = (2+a)/c
    headroom = c-1-a
    if n and headroom <= 0:
        raise ValueError("This ladder length is not strictly feasible at c")
    epsilon = (c-1)*headroom/4 if n else Fraction(0)
    points = [Fraction(1)]
    for _ in range(n):
        points.append((2+points[-1]+epsilon)/c)
    if n:
        assert points[-1] < c-1
        assert all(2+a < c*b for a, b in zip(points, points[1:]))
    return [Fraction(0)] + [a/points[-1] for a in points]


def maximum_length(c, cap=100):
    a, n = Fraction(1), 0
    while (2+a)/c < c-1 and n < cap:
        a, n = (2+a)/c, n+1
    return n


def numerator(p, q, r, n):
    # Exact formula for the ladder event polynomial; n=None is the N->infty limit.
    tail_factor = 1 if n is None else Fraction(n-1, n)
    return (p**3*(q+r) + 3*p*p*(q+r)**2
            + 3*p*(q**3+3*q*q*r+2*q*r*r+r**3)
            + q**3*r + Fraction(3, 2)*q*q*r*r*tail_factor)


def masses_for_length(n):
    def objective(z):
        p, q = z
        r = 1-p-q
        return -float(numerator(p, q, r, n))/(1-p**4)
    best = None
    for p in (.2, .35, .5):
        for q in (.3, .45, .6):
            r = minimize(objective, [p, min(q, 1-p-.01)], method="SLSQP",
                         bounds=[(0, .999), (0, 1)],
                         constraints=[{"type": "ineq", "fun": lambda z: 1-z.sum()}],
                         options={"ftol": 1e-13, "maxiter": 500})
            if r.success and (best is None or r.fun < best.fun):
                best = r
    if best is None:
        raise RuntimeError("Mass optimization failed")
    p, q = [Fraction(round(float(v)*10**12), 10**12) for v in best.x]
    r = 1-p-q
    assert min(p, q, r) >= 0
    value = numerator(p, q, r, n)/(1-p**4)
    return p, q, r, value


def quantile_start(support, masses, rho, m, levels=3):
    atoms = [(Fraction(0), masses[0]**levels)]
    for k in range(levels):
        atoms.extend((rho**k*a, masses[0]**k*w) for a, w in zip(support[1:], masses[1:]))
    atoms.sort()
    values = []
    for i in range(m):
        target, cumulative = Fraction(2*i+1, 2*m), Fraction(0)
        for value, weight in atoms:
            cumulative += weight
            if cumulative >= target:
                values.append(float(value))
                break
    return values


def analyze(c, sample_m=None):
    if not 2 < c or (c-1)**2 >= 2:
        raise ValueError("Require 2<c<1+sqrt(2)")
    n = maximum_length(c)
    if n == 0:
        raise ValueError("Use recursive.py for the single positive-atom block below the first transition")
    support = block(c, n)
    p, q, r, value = masses_for_length(n)
    masses = [p, q] + [r/n]*n
    terms, slack = event_polynomial(support, c)
    # Independently enumerate all strict events to verify the closed formula.
    assert exact_probability(terms, masses) == numerator(p, q, r, n)
    rho = min(slack/6, support[1]/(2*c), Fraction(1, 2))
    result = {
        "c": str(c), "c_decimal": float(c), "tail_atoms": n,
        "support_exact": [str(a) for a in support], "support": [float(a) for a in support],
        "masses_exact": [str(w) for w in masses], "masses": [float(w) for w in masses],
        "recursive_probability_exact": str(value), "recursive_probability": float(value),
        "safe_scale_ratio_exact": str(rho), "safe_scale_ratio": float(rho),
        "polynomial_verified_exactly": True,
        "interpretation": "Certified achieved lower bound; local mass optimization; no upper bound on all laws.",
    }
    if sample_m:
        result["m"] = sample_m
        result["x"] = quantile_start(support, masses, rho, sample_m)
        result["x_interpretation"] = "Quantiles of a three-level construction, for a MILP warm start."
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--c", nargs="+", required=True)
    p.add_argument("--sample-m", type=int)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    cases = [analyze(Fraction(c), args.sample_m) for c in args.c]
    if len(cases) == 1:
        result = cases[0]
    else:
        result = {"cases": cases}
    p0, q, r, value = masses_for_length(None)
    result["infinite_ladder_numerical_mass_optimum"] = {
        "p0": float(p0), "main_mass": float(q), "tail_mass": float(r), "probability": float(value),
        "interpretation": "Numerical optimization of the limiting family formula, not a universal upper bound.",
    }
    def transition(n):
        def f(c):
            a = 1
            for _ in range(n):
                a = (2+a)/c
            return c-1-a
        return brentq(f, 2, 1+2**.5)
    result["first_six_ladder_thresholds"] = [transition(n) for n in range(1, 7)]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    for case in cases:
        print(f"c={case['c_decimal']:g}; tail atoms={case['tail_atoms']}; "
              f"recursive probability={case['recursive_probability']:.12f}")
    print(f"Infinite-ladder family, optimized numerically: {float(value):.12f}")


if __name__ == "__main__":
    main()
