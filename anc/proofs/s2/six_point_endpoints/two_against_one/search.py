"""Two-against-one MILP discovery and exact recursive-law certification.

The MILP optimizes a fixed positive margin; its bound is NOT an upper bound
on S_2(c). Mass optimization is local. Exported lower bounds use Fractions.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
import json
from math import comb
from pathlib import Path

import gurobipy as gp
import numpy as np
from scipy.optimize import minimize


def tuples(m, mode):
    if mode == "distinct":
        ts = [(i, j, k) for q in combinations(range(m), 3)
              for k in q[1:] for i, j in [tuple(v for v in q if v != k)]]
        return ts, [1]*len(ts), 3*comb(m, 3)
    ts = [(i, j, k) for i, j in combinations_with_replacement(range(m), 2)
          for k in range(m) if i < k]
    return ts, [1 if i == j else 2 for i, j, k in ts], m**3


def events(support, c):
    terms = Counter()
    slack = []
    for i, j, k in product(range(len(support)), repeat=3):
        d = c*support[k]-support[i]-support[j]
        if d > 0:
            terms[tuple((i, j, k).count(v) for v in range(len(support)))] += 1
            slack.append(d)
    return terms, min(slack)


def exact_value(terms, masses):
    value = Q(0)
    for powers, coef in terms.items():
        term = Q(coef)
        for mass, power in zip(masses, powers):
            term *= mass**power
        value += term
    return value


def optimize(support, c, starts=16, seed=0):
    support = sorted(set(map(Q, support)))
    support = [v/support[-1] for v in support]
    assert support[0] == 0 and support[1] > 0
    terms, d = events(support, c)
    powers = np.array(list(terms))
    coeff = np.array(list(terms.values()))
    n = len(support)

    def objective(p):
        monomials = np.prod(p**powers, axis=1)
        f = coeff @ monomials
        den = (1-p[0])*(1+p[0]+p[0]**2)
        grad = np.empty(n)
        for j in range(n):
            exponents = powers.copy()
            exponents[:, j] = np.maximum(0, exponents[:, j]-1)
            grad[j] = (coeff*powers[:, j]) @ np.prod(p**exponents, axis=1)
        grad = -grad/den
        grad[0] -= 3*p[0]**2*f/den**2
        return -f/den, grad

    rng = np.random.default_rng(seed)
    best = None
    for trial in range(starts):
        p = np.full(n, 1/n) if trial == 0 else rng.dirichlet(np.ones(n))
        r = minimize(objective, p, jac=True, method="SLSQP",
                     bounds=[(0, 1-1e-6)]+[(0, 1)]*(n-1),
                     constraints=[{"type": "eq", "fun": lambda p: p.sum()-1,
                                   "jac": lambda p: np.ones(n)}],
                     options={"ftol": 2e-13, "maxiter": 600})
        nums = [max(0, round(float(v)*10**12)) for v in r.x]
        if not sum(nums[1:]):
            continue
        masses = [Q(v, sum(nums)) for v in nums]
        f = exact_value(terms, masses)
        value = f/(1-masses[0]**3)
        if best is None or value > best[0]:
            best = value, masses, f
    value, masses, f = best
    # Replace zero by a rho-scaled copy. A positive RHS base success loses
    # at most 2*rho of margin; a zero RHS cannot beat a positive LHS.
    rho = min(d/4, support[1]/(2*c), Q(1, 2))
    assert 2*rho < d and c*rho < support[1] and rho < support[1]
    return {"support": list(map(float, support)), "support_exact": list(map(str, support)),
            "masses": list(map(float, masses)), "masses_exact": list(map(str, masses)),
            "value": float(value), "value_exact": str(value), "base_exact": str(f),
            "rho_exact": str(rho), "slack_exact": str(d),
            "terms": [{"powers": list(e), "coefficient": k} for e, k in sorted(terms.items())]}


def solve(m, c, mode, seconds, margin, seed=0, start=None, progress=False):
    env = gp.Env(empty=True)
    env.setParam("OutputFlag", 0)
    env.start()
    model = gp.Model(env=env)
    model.Params.Threads = 4
    model.Params.TimeLimit = seconds
    model.Params.FeasibilityTol = 1e-9
    model.Params.IntFeasTol = 1e-9
    model.Params.IntegralityFocus = 1
    model.Params.MIPGap = 0
    model.Params.Seed = seed
    x = model.addVars(m, lb=0, ub=1)
    model.addConstr(x[0] == 0)
    model.addConstr(x[m-1] == 1)
    for i in range(m-1):
        model.addConstr(x[i] <= x[i+1])
    ts, weights, den = tuples(m, mode)
    y = model.addVars(ts, vtype=gp.GRB.BINARY)
    for i, j, k in ts:
        model.addGenConstrIndicator(y[i, j, k], True,
                                   x[i]+x[j]-float(c)*x[k] <= -margin)
        for u in [(i+1, j, k), (i, j+1, k), (i, j, k-1)]:
            if u in y:
                model.addConstr(y[u] <= y[i, j, k])
    if mode == "distinct":
        for i, j, k in combinations(range(m), 3):
            model.addConstr(y[i, k, j] <= y[i, j, k])
    values = start or [0.]*(m//3)+[1.]*(m-m//3)
    for i, v in enumerate(values):
        x[i].Start = v
    for i, j, k in ts:
        y[i, j, k].Start = int(float(c)*values[k]-values[i]-values[j] >= margin)
    model.setObjective(gp.quicksum(w*y[t] for t, w in zip(ts, weights)), gp.GRB.MAXIMIZE)
    last_report = -30.

    def report(mdl, where):
        nonlocal last_report
        if where == gp.GRB.Callback.MIP:
            elapsed = mdl.cbGet(gp.GRB.Callback.RUNTIME)
            if elapsed-last_report >= 30:
                print(json.dumps({"type": "progress", "c": str(c),
                                  "seconds": round(elapsed, 1),
                                  "incumbent": mdl.cbGet(gp.GRB.Callback.MIP_OBJBST),
                                  "bound": mdl.cbGet(gp.GRB.Callback.MIP_OBJBND)}), flush=True)
                last_report = elapsed

    model.optimize(report if progress else None)
    result = {"m": m, "c": str(c), "mode": mode, "margin": margin,
              "status": model.Status, "bound": model.ObjBound, "denominator": den,
              "runtime": model.Runtime, "seed": seed, "time_limit": seconds}
    if model.SolCount:
        selected = [t for t in ts if y[t].X > .5]
        result["objective"] = round(model.ObjVal)
        lp = gp.Model(env=env)
        lp.Params.FeasibilityTol = 1e-9
        z = lp.addVars(m, lb=0, ub=1)
        delta = lp.addVar(lb=0)
        lp.addConstr(z[0] == 0)
        lp.addConstr(z[m-1] == 1)
        for i in range(m-1):
            lp.addConstr(z[i] <= z[i+1])
        for i, j, k in selected:
            lp.addConstr(float(c)*z[k]-z[i]-z[j] >= delta)
        lp.setObjective(delta, gp.GRB.MAXIMIZE)
        lp.optimize()
        raw = [z[i].X for i in range(m)]
        vals = []
        for v in raw:
            vals.append(max(vals[-1] if vals else 0., min(1., v)))
        # Round a maximum-margin witness, then check ALL selected events exactly.
        xs = [Q(str(round(v, 14))) for v in vals]
        assert all(xs[i] <= xs[i+1] for i in range(m-1))
        assert all(c*xs[k] > xs[i]+xs[j] for i, j, k in selected)
        result.update(x=list(map(float, xs)), x_exact=list(map(str, xs)),
                      polished_raw_x=raw,
                      order_roundoff_correction=max(abs(a-b) for a, b in zip(raw, vals)),
                      polished_margin=delta.X, selected=selected, exact_selected_check=True)
        iid_count = sum(c*xs[k] > xs[i]+xs[j] for i, j, k in product(range(m), repeat=3))
        result["empirical_iid"] = iid_count/m**3
        result["empirical_iid_exact"] = str(Q(iid_count, m**3))
        lp.dispose()
    model.dispose()
    env.dispose()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", nargs="+", required=True)
    parser.add_argument("--m", type=int, default=12)
    parser.add_argument("--mode", choices=["distinct", "iid"], default="distinct")
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--margin", type=float, default=2e-6)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--starts", type=int, default=16)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    previous = None
    for cs in args.c:
        c = Q(cs)
        assert 1 < c < 2
        result = solve(args.m, c, args.mode, args.seconds, args.margin, args.seed, previous)
        if "x" in result:
            previous = result["x"]
            support = sorted(set(map(Q, result["x_exact"])))
            blocks = []
            # Full support plus suffix blocks, always with a recursive zero.
            for cutoff in [Q(0), Q(1, 5), Q(1, 2), 1/c]:
                block = [Q(0)]+[v for v in support if v > cutoff]
                if block in blocks:
                    continue
                blocks.append(block)
            result["laws"] = [optimize(block, c, args.starts, args.seed) for block in blocks]
            result["best_value"] = max(v["value"] for v in result["laws"])
        path = args.output/f"m{args.m}_c{c.numerator}_{c.denominator}_{args.mode}_s{args.seed}.json"
        path.write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({k: result.get(k) for k in ["m", "c", "mode", "status", "objective", "bound", "x", "best_value"]}), flush=True)


if __name__ == "__main__":
    main()
