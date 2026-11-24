"""Optimize masses on a block repeated at arbitrarily small scales.

For a base law on {0,a1,...,ak}, with masses p0,p1,...,pk, replace
the zero atom recursively by a sufficiently small scaled copy of the law.
The resulting probability is F(p)/(1-p0**4). Exact rational checks below
certify the achieved value, not global optimality of the mass optimization.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def event_polynomial(support, c):
    terms = Counter()
    positive_slacks = []
    n = len(support)
    for t in product(range(n), repeat=4):
        slack = c * support[t[3]] - sum(support[i] for i in t[:3])
        if slack > 0:
            terms[tuple(t.count(i) for i in range(n))] += 1
            positive_slacks.append(slack)
    return terms, min(positive_slacks)


def exact_probability(terms, masses):
    return sum(coef * product_fraction(p**e for p, e in zip(masses, exponents))
               for exponents, coef in terms.items())


def product_fraction(values):
    result = Fraction(1)
    for v in values:
        result *= v
    return result


def optimize_block(support, c, starts=24, seed=0):
    support = sorted(set(map(Fraction, support)))
    if len(support) < 2 or support[0] != 0 or support[-1] <= 0:
        raise ValueError("Require zero and at least one positive support point")
    support = [v / support[-1] for v in support]
    terms, min_slack = event_polynomial(support, c)
    powers = np.array(list(terms), dtype=int)
    coeffs = np.array(list(terms.values()), dtype=float)
    n = len(support)

    def objective(p):
        numerator = np.dot(coeffs, np.prod(p**powers, axis=1))
        denominator = (1-p[0]) * (1+p[0]+p[0]**2+p[0]**3)
        return -numerator / denominator

    rng = np.random.default_rng(seed)
    trials = []
    for trial in range(starts):
        initial = np.full(n, 1/n) if trial == 0 else rng.dirichlet(np.ones(n))
        r = minimize(objective, initial, method="SLSQP",
                     bounds=[(0, 1-1e-7)] + [(0, 1)] * (n-1),
                     constraints=[{"type": "eq", "fun": lambda p: p.sum()-1}],
                     options={"ftol": 1e-13, "maxiter": 1000})
        # Turn every candidate into a feasible rational probability vector,
        # then rank candidates by their exact achieved values.
        numerators = [max(0, round(float(v) * 10**12)) for v in r.x]
        if sum(numerators[1:]) == 0:
            continue
        masses = [Fraction(v, sum(numerators)) for v in numerators]
        f = exact_probability(terms, masses)
        value = f / (1-masses[0]**4)
        trials.append((value, masses, bool(r.success)))
    if not trials:
        raise RuntimeError("No feasible mass vector found")
    value, masses, success = max(trials, key=lambda t: t[0])
    # Any base success has positive RHS; perturbing its zero LHS slots adds
    # at most 3*rho < min_slack. If the base RHS is zero but some LHS slot
    # is positive, c*rho < min_positive prevents a new success. All-zero
    # draws recurse. Other failed events stay failed as their LHS increases.
    rho = min(min_slack/6, support[1]/(2*c), Fraction(1, 2))
    assert 3*rho < min_slack and c*rho < support[1] and rho < support[1]
    f = exact_probability(terms, masses)
    return {
        "c": str(c), "c_decimal": float(c),
        "support_exact": [str(v) for v in support],
        "support": [float(v) for v in support],
        "masses_exact": [str(p) for p in masses], "masses": [float(p) for p in masses],
        "base_probability_exact": str(f), "base_probability": float(f),
        "recursive_probability_exact": str(value), "recursive_probability": float(value),
        "above_half_exact": value > Fraction(1, 2),
        "safe_scale_ratio_exact": str(rho), "safe_scale_ratio": float(rho),
        "minimum_base_success_slack_exact": str(min_slack),
        "terms": [{"powers": list(e), "coefficient": coef} for e, coef in sorted(terms.items())],
        "starts": starts, "best_optimizer_success": success,
        "trial_value_min": float(min(t[0] for t in trials)),
        "trial_value_max": float(max(t[0] for t in trials)),
        "interpretation": "Exact achieved lower bound from rational masses; mass optimization is local, not a global upper bound.",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--c", help="Decimal or rational; defaults to the source coefficient")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument("--x", nargs="+", help="Base support, including zero")
    group.add_argument("--source", type=Path, help="A solver result; uses its maximum-margin representative")
    p.add_argument("--top-min", type=float, default=.5,
                   help="For --source, keep zero and support values >= this cutoff; use 0 for all scales")
    p.add_argument("--starts", type=int, default=24)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.source:
        source = json.loads(args.source.read_text())
        c = Fraction(args.c or source["c"])
        representative = source.get("max_margin_representative") or source
        values = [v for v in representative["x"] if v >= args.top_min]
        support = [Fraction(0)]
        for v in sorted(values):
            if abs(float(support[-1]) - v) > 1e-8:
                support.append(Fraction(str(v)))
    else:
        if not args.c:
            p.error("--c is required with --x")
        c, support = Fraction(args.c), list(map(Fraction, args.x))
    if not 2 < c < 3 or args.starts < 1:
        p.error("Require 2<c<3 and --starts>=1")
    r = optimize_block(support, c, args.starts)
    if args.source:
        r["source"] = str(args.source)
        r["top_min"] = args.top_min
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(r, indent=2, allow_nan=False) + "\n")
    print(f"c={float(c):g}; block={r['support']}; masses={r['masses']}; "
          f"recursive probability={r['recursive_probability']:.12f}; "
          f">1/2: {r['above_half_exact']}")


if __name__ == "__main__":
    main()
