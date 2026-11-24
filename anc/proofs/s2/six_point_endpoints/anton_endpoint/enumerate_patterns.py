"""Complete strict-pattern cover with exact Q(sqrt(2)) pruning certificates.

The numerical LP proposes exclusions; an exclusion is used only after exact
verification. Extra leaves are harmless. No fixed-margin cutoff bounds x:
homogeneity permits every strict realization to be scaled to unit margins.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import time

import gurobipy as gp
import numpy as np

from quadratic import Q2, solve_linear


def candidates(n, c2=False, summands=3):
    if summands == 2:
        return tuple((i, j, k) for i, j in combinations(range(n), 2)
                     for k in range(n) if k not in (i, j) and k > i)
    if summands != 3:
        raise ValueError("Unsupported event arity")
    return tuple((i, j, k, ell) for i, j, k in combinations(range(n), 3)
                 for ell in range(n) if ell not in (i, j, k) and ell > (j if c2 else i))


def gap_rows(n, tuples, c):
    return [[Q2(sum(i >= h for i in t[:-1]))-c*int(t[-1] >= h)
             for h in range(n)] for t in tuples]


def certificate(rows, signs, ray):
    scale = max(abs(v) for v in ray)
    if not scale:
        return None
    active = [i for i, v in enumerate(ray) if v > scale*1e-9]
    if not active:
        return None
    h = [[signs[i]*v for v in rows[i]] for i in active]

    def valid(weights):
        return weights is not None and any(weights) and all(w.sign() >= 0 for w in weights) and all(
            sum(w*row[j] for w, row in zip(weights, h)).sign() >= 0 for j in range(len(h[0])))

    # Most rays have simple rational weights. Degenerate endpoint rays may
    # instead require algebraic weights, reconstructed from their zero slacks.
    weights = [Q2(Fraction(ray[i]/scale).limit_denominator(10000)) for i in active]
    if not valid(weights):
        numerical = np.array([[float(v) for v in row] for row in h])
        w = np.array([ray[i]/scale for i in active])
        slack = w @ numerical
        zeros = [j for j, v in enumerate(slack) if abs(v) < 1e-7*max(1, sum(w))]
        equations = [[row[j] for row in h] for j in zeros]+[[Q2(1)]*len(h)]
        weights = solve_linear(equations, [Q2()]*len(zeros)+[Q2(1)])
    if not valid(weights):
        return None
    return {str(i): w.json() for i, w in zip(active, weights) if w}


def verify_cover(data):
    n = data["size"]
    c = Q2(*data["coefficient"])
    summands = data.get("summands", 3)
    if summands == 2:
        if c.b or (c-Q2(1)).sign() <= 0 or (Q2(2)-c).sign() <= 0 or data["c2_regression"]:
            raise ValueError("Two-summand covers require rational 1<c<2")
    elif c != (Q2(2) if data["c2_regression"] else Q2(1, 1)):
        raise ValueError("Coefficient does not match the candidate-set convention")
    tuples = [tuple(t) for t in data["tuples"]]
    if tuples != list(candidates(n, data["c2_regression"], summands)):
        raise ValueError("Candidate tuple mismatch")
    rows, intervals = gap_rows(n, tuples, c), []
    width = len(tuples)
    for prefix, encoded in data["pruned"].items():
        if not prefix or len(prefix) > width or set(prefix)-{"+", "-"}:
            raise ValueError("Invalid prefix")
        weights = {int(i): Q2(*v) for i, v in encoded.items()}
        if not weights or any(i < 0 or i >= len(prefix) for i in weights):
            raise ValueError("Invalid support")
        if any(w.sign() < 0 for w in weights.values()) or not any(weights.values()):
            raise ValueError("Invalid weights")
        for j in range(n):
            value = sum(w*(1 if prefix[i] == "+" else -1)*rows[i][j] for i, w in weights.items())
            if value.sign() < 0:
                raise ValueError("Invalid exact pruning certificate")
        left = int("".join("1" if s == "+" else "0" for s in prefix), 2) << (width-len(prefix))
        intervals.append((left, left+(1 << (width-len(prefix)))))
    for leaf in data["patterns"]:
        if len(leaf) != width or set(leaf)-{"+", "-"}:
            raise ValueError("Invalid leaf")
        left = int("".join("1" if s == "+" else "0" for s in leaf), 2)
        intervals.append((left, left+1))
    cursor = 0
    for left, right in sorted(intervals):
        if left != cursor:
            raise ValueError("The pattern cover has a gap or overlap")
        cursor = right
    if cursor != 1 << width:
        raise ValueError("Incomplete pattern cover")
    return True


def enumerate_cover(size, seconds, c2=False, previous=None, coefficient=None, summands=3,
                    backend="gurobi"):
    c = Q2(coefficient) if coefficient is not None else (Q2(2) if c2 else Q2(1, 1))
    if summands == 2 and (c.b or not 1 < c.a < 2 or c2):
        raise ValueError("Two-summand covers require rational 1<c<2")
    ts = candidates(size, c2, summands)
    rows = gap_rows(size, ts, c)
    if backend == "highs":
        import highspy
        model = highspy.Highs()
        model.setOptionValue("output_flag", False)
        # Keep HiGHS' automatic thread setting. Its scheduler is shared
        # process-wide: forcing one thread after another LP initialized it
        # makes run() fail, even for these small serial simplex problems.
        model.setOptionValue("solver", "simplex")
        model.setOptionValue("presolve", "off")
        model.setOptionValue("primal_feasibility_tolerance", 1e-9)
        model.setOptionValue("dual_feasibility_tolerance", 1e-9)
        model.addCols(size, np.ones(size), np.zeros(size),
                      np.full(size, highspy.kHighsInf), 0,
                      np.zeros(size+1, dtype=np.int32), np.array([], dtype=np.int32),
                      np.array([], dtype=float))
    elif backend == "gurobi":
        env = gp.Env(empty=True)
        env.setParam("OutputFlag", 0)
        env.start()
        model = gp.Model(env=env)
        model.Params.Method = 1
        model.Params.InfUnbdInfo = 1
        model.Params.DualReductions = 0
        model.Params.FeasibilityTol = 1e-9
        model.Params.Threads = 1
        d = model.addVars(size, lb=0)
        model.setObjective(gp.quicksum(d.values()))
    else:
        raise ValueError("Unknown LP backend")
    constraints, signs = [], []
    if previous and (previous["size"] != size or previous["coefficient"] != c.json()
                     or previous.get("summands", 3) != summands):
        raise ValueError("Incompatible resume file")
    leaves = list(previous["patterns"]) if previous else []
    pruned = dict(previous["pruned"]) if previous else {}
    covered = set(leaves) | set(pruned)
    for length in range(len(ts), 0, -1):
        for key in [p for p in covered if len(p) == length]:
            parent = key[:-1]
            if parent+"+" in covered and parent+"-" in covered:
                covered.add(parent)
    nodes = previous["lp_calls"] if previous else 0
    rejected = previous["unverified_rays"] if previous else 0
    tick, next_report = time.monotonic(), 20

    def visit():
        nonlocal nodes, next_report, rejected
        if "".join("+" if s == 1 else "-" for s in signs) in covered:
            return
        elapsed = time.monotonic()-tick
        if elapsed > seconds:
            raise TimeoutError
        if elapsed > next_report:
            print(f"{elapsed:.1f}s: {nodes} LPs, {len(leaves)} leaves, {len(pruned)} exact exclusions, {rejected} unverified rays", flush=True)
            next_report = elapsed+20
        if len(signs) == len(ts):
            leaves.append("".join("+" if s == 1 else "-" for s in signs))
            return
        i = len(signs)
        if backend == "gurobi":
            expr = gp.quicksum(float(v)*d[j] for j, v in enumerate(rows[i]) if v)
        for sign in (1, -1):
            signs.append(sign)
            if "".join("+" if s == 1 else "-" for s in signs) in covered:
                signs.pop()
                continue
            if backend == "highs":
                model.addRow(-highspy.kHighsInf, -1., size,
                             np.arange(size, dtype=np.int32),
                             np.array([sign*float(v) for v in rows[i]]))
                run_status = model.run()
                if run_status == highspy.HighsStatus.kError:
                    raise RuntimeError('HiGHS failed to run the pattern feasibility LP')
                status = model.getModelStatus()
                infeasible = status == highspy.HighsModelStatus.kInfeasible
                if status not in (highspy.HighsModelStatus.kOptimal,
                                   highspy.HighsModelStatus.kInfeasible):
                    # Exact exclusions, rather than numerical LP statuses,
                    # decide which branches can be discarded.
                    infeasible = False
            else:
                constraints.append(model.addConstr(sign*expr <= -1))
                model.optimize()
                infeasible = model.Status == gp.GRB.INFEASIBLE
            nodes += 1
            if infeasible:
                if backend == "highs":
                    _, exists, dual = model.getDualRay()
                    ray = -np.asarray(dual) if exists else np.zeros(len(signs))
                else:
                    ray = model.getAttr("FarkasDual", constraints)
                cert = certificate(rows, signs, ray)
                if cert is not None:
                    pruned["".join("+" if s == 1 else "-" for s in signs)] = cert
                else:
                    rejected += 1
                    visit()
            else:
                visit()
            if backend == "highs":
                model.deleteRows(1, np.array([len(signs)-1], dtype=np.int32))
            else:
                model.remove(constraints.pop())
            signs.pop()

    complete = True
    try:
        visit()
    except TimeoutError:
        complete = False
    result = {"size": size, "coefficient": c.json(), "c2_regression": c2,
              "summands": summands, "tuples": ts, "patterns": leaves, "pruned": pruned,
              "complete": complete, "lp_calls": nodes, "unverified_rays": rejected,
              "seconds": time.monotonic()-tick+(previous["seconds"] if previous else 0)}
    if backend == "gurobi":
        model.dispose()
        env.dispose()
    if complete:
        verify_cover(result)
        result["exact_cover_verified"] = True
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--size", type=int, default=6)
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--c2-regression", action="store_true")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--verify", action="store_true")
    p.add_argument("--resume", action="store_true")
    args = p.parse_args()
    if args.verify:
        data = json.loads(args.output.read_text())
        verify_cover(data)
        print("Exact cover verified:", len(data["patterns"]), "patterns")
        return
    previous = json.loads(args.output.read_text()) if args.resume else None
    result = enumerate_cover(args.size, args.seconds, args.c2_regression, previous)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, separators=(",", ":"))+"\n")
    print({k: v for k, v in result.items() if k not in ("tuples", "patterns", "pruned")}, flush=True)
    print("patterns", len(result["patterns"]), "pruned", len(result["pruned"]), flush=True)


if __name__ == "__main__":
    main()
