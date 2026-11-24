"""Six-point flag certificates for P(X1+X2<c X3), at rational c.

Enumeration is resumable. Incomplete covers NEVER yield an upper bound.
Only independent exact verification makes a numerical fit a certificate.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "anton_endpoint"))
from enumerate_patterns import enumerate_cover, verify_cover
from flag_sdp import assemble, fit, scores, certify
from verify_sdp import verify
import numpy as np


def polynomial(c, n):
    return c**(n+1)-2-sum(c**j for j in range(1, n))


def bracket(n, epsilon):
    if n < 1 or epsilon <= 0:
        raise ValueError("Require N>=1 and epsilon>0")
    lo, hi = Q(1), Q(2)
    while hi-lo > min(epsilon/100, Q(1, 10**12)):
        mid = (lo+hi)/2
        if polynomial(mid, n) > 0:
            hi = mid
        else:
            lo = mid
    # Keep endpoint arithmetic small, and verify the polynomial signs exactly.
    scale = 10**12
    center = Q(int((lo+hi)/2*scale), scale)
    a, b = center-epsilon, center+epsilon
    if not 1 < a < b < 2 or not polynomial(a, n) < 0 < polynomial(b, n):
        raise ValueError("epsilon too small or bracket outside (1,2)")
    return a, b


def save(path, data):
    path.write_text(json.dumps(data, indent=2)+"\n")


def lower_bound(c, directories):
    """Recheck saved recursive constructions at this c, using exact arithmetic."""
    from search import events, exact_value
    best, source = Q(0), None
    for directory in directories:
        for path in directory.glob("m*.json"):
            data = json.loads(path.read_text())
            # A law discovered at a larger scan coefficient may still work
            # here. Recompute all strict events and the recursive scale
            # condition at this c instead of filtering by its source label.
            for law in data.get("laws", []):
                xs = list(map(Q, law["support_exact"]))
                masses = list(map(Q, law["masses_exact"]))
                if (len(xs) != len(masses) or len(xs) < 2 or xs[0] != 0
                    or xs[-1] != 1 or any(a >= b for a, b in zip(xs, xs[1:]))
                    or any(w < 0 for w in masses) or sum(masses) != 1 or masses[0] == 1):
                    raise ValueError(f"Invalid law: {path}")
                terms, slack = events(xs, c)
                rho = min(slack/4, xs[1]/(2*c), Q(1, 2))
                assert 2*rho < slack and c*rho < xs[1]
                value = exact_value(terms, masses)/(1-masses[0]**3)
                if value > best:
                    best, source = value, str(path)
    return {"exact": str(best), "decimal": float(best), "source": source}


def run(c, output, args):
    folder = output/f"c{c.numerator}_{c.denominator}"
    folder.mkdir(parents=True, exist_ok=True)
    cover_path, cert_path = folder/"cover.json", folder/"certificate.json"
    data = json.loads(cover_path.read_text()) if cover_path.exists() else None
    if data and (data["coefficient"] != [str(c), "0"] or data.get("summands") != 2 or data["size"] != 6):
        raise ValueError("Incompatible cached cover")
    if args.phase in ("all", "enumerate") and (not data or not data["complete"]):
        data = enumerate_cover(6, args.enumeration_seconds, previous=data,
                               coefficient=c, summands=2, backend=args.lp_backend)
        # JSON normalization ensures tuple lists match independently read certificates.
        save(cover_path, data)
        data = json.loads(cover_path.read_text())
    row = {"c": str(c), "c_decimal": float(c), "directory": str(folder),
           "complete_cover": bool(data and data["complete"])}
    if not row["complete_cover"]:
        row["status"] = "incomplete cover: rerun to resume; no upper bound"
        return row
    verify_cover(data)
    row.update(patterns=len(data["patterns"]), enumeration_seconds=data["seconds"])
    if args.phase == "enumerate":
        return row
    if args.phase in ("all", "solve"):
        tick = time.monotonic()
        patterns, objective, blocks = assemble(data)
        active = set(np.argsort(objective)[-args.initial:].tolist())
        active.update(np.random.default_rng(42).choice(len(patterns), min(args.initial, len(patterns)), replace=False).tolist())
        # The constant iid law realizes the all-failure row. Keeping it in
        # every restricted problem prevents artificial primal infeasibility.
        active.update(i for i, pattern in enumerate(data["patterns"]) if "+" not in pattern)
        history, best = [], None
        if cert_path.exists():
            best = Q(verify(data, json.loads(cert_path.read_text()))["exact_bound"])
        for iteration in range(args.rounds):
            selected = np.array(sorted(active))
            info, matrices, weights = fit(objective, blocks, selected, args.sdp_seconds, 1e-8)
            if not all(np.isfinite(q).all() for q in matrices):
                raise ValueError("Solver returned nonfinite factors")
            values = scores(objective, blocks, matrices)
            # Both three- and four-variable events have denominator 60 at order six.
            bound, cert = certify(patterns.tolist(), blocks, matrices, 10)
            cert.update(summands=2, coefficient=data["coefficient"], tuples=data["tuples"],
                        exact_bound=str(bound), cover=str(cover_path))
            cert = json.loads(json.dumps(cert))
            checked = verify(data, cert)
            if best is None or bound < best:
                best = bound
                save(cert_path, cert)
                save(folder/"verification.json", checked)
            info.update(round=iteration+1, active=len(active), exact_bound=str(bound),
                        exact_bound_decimal=float(bound))
            history.append(info)
            print(json.dumps({"c": str(c), **info}), flush=True)
            save(folder/"report.json", {"c": str(c), "patterns": len(patterns),
                 "dimensions": [len(b["flags"]) for b in blocks], "history": history,
                 "best_exact_bound": str(best), "seconds": time.monotonic()-tick})
            violations = np.flatnonzero(values > info["dual"]+2e-7)
            new = set(violations[np.argsort(values[violations])[-args.add:]].tolist())-active
            if not new:
                break
            active.update(new)
    if not cert_path.exists():
        row["status"] = "no certificate yet"
        return row
    checked = verify(data, json.loads(cert_path.read_text()))
    save(folder/"verification.json", checked)
    row.update(status="independently verified", upper_exact=checked["exact_bound"],
               upper=checked["decimal_bound"], lower=lower_bound(c, args.lower_results))
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    group = p.add_mutually_exclusive_group()
    group.add_argument("--c", nargs="+", type=Q)
    group.add_argument("--N", nargs="+", type=int, help="Ladder indices (default: 3 4)")
    p.add_argument("--epsilon", type=Q, default=Q("0.00001"))
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--phase", choices=["all", "enumerate", "solve", "verify"], default="all")
    p.add_argument("--lp-backend", choices=["gurobi", "highs"], default="gurobi")
    p.add_argument("--enumeration-seconds", type=float, default=300)
    p.add_argument("--sdp-seconds", type=float, default=120, help="Per SDP round, not total")
    p.add_argument("--rounds", type=int, default=6)
    p.add_argument("--initial", type=int, default=500)
    p.add_argument("--add", type=int, default=500)
    p.add_argument("--lower-results", nargs="+", type=Path,
                   default=[HERE/"results/refine_m12", HERE/"results/scan_m12"])
    args = p.parse_args()
    if min(args.enumeration_seconds, args.sdp_seconds, args.rounds, args.initial, args.add) <= 0:
        p.error("Limits and batch sizes must be positive")
    pairs = [(n, *bracket(n, args.epsilon)) for n in (args.N or [3, 4])] if not args.c else []
    cs = sorted(set(args.c or [v for _, a, b in pairs for v in (a, b)]))
    if not all(1 < c < 2 for c in cs):
        p.error("Require rational 1<c<2")
    args.output.mkdir(parents=True, exist_ok=True)
    rows = []
    for c in cs:
        print(f"Starting c={c} ({float(c):.12f}), phase={args.phase}", flush=True)
        rows.append(run(c, args.output, args))
        save(args.output/"summary.json", {"rows": rows})
    by_c = {Q(r["c"]): r for r in rows}
    comparisons = []
    for n, a, b in pairs:
        left, right = by_c[a], by_c[b]
        item = {"N": n, "c_below": str(a), "c_above": str(b),
                "increase_certified": None}
        if "upper_exact" in left and "lower" in right:
            item["increase_certified"] = Q(right["lower"]["exact"]) > Q(left["upper_exact"])
            item["separation_exact"] = str(Q(right["lower"]["exact"])-Q(left["upper_exact"]))
        comparisons.append(item)
    summary = {"rows": rows, "thresholds": comparisons,
               "interpretation": "Only lower(c_above)>upper(c_below) certifies an increase across a bracket. Neither changes in SDP bounds nor failure to separate decide sharpness or discontinuity at c_N."}
    save(args.output/"summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
