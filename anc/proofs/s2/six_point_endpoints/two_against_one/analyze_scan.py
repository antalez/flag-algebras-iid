"""Summarize fixed-margin MILP scans and continue new patterns by LP."""
import argparse
import json
from math import sqrt
from pathlib import Path


def pattern_threshold(data):
    import numpy as np
    from scipy.optimize import linprog
    m = data["m"]
    selected = data["selected"]
    def slack(c):
        rows = []
        for i in range(m-1):
            r = np.zeros(m+1)
            r[i], r[i+1] = 1, -1
            rows.append(r)
        for i, j, k in selected:
            r = np.zeros(m+1)
            r[i] += 1
            r[j] += 1
            r[k] -= c
            r[-1] = 1
            rows.append(r)
        objective = np.zeros(m+1)
        objective[-1] = -1
        result = linprog(objective, A_ub=np.array(rows), b_ub=np.zeros(len(rows)),
                         bounds=[(0, 0)]+[(0, 1)]*(m-2)+[(1, 1), (0, None)],
                         method="highs", options={"primal_feasibility_tolerance": 1e-9,
                                                   "dual_feasibility_tolerance": 1e-9})
        return result.x[-1] if result.success else 0
    lo, hi = 1., float(__import__("fractions").Fraction(data["c"]))
    for _ in range(36):
        mid = (lo+hi)/2
        if slack(mid) > 2e-9:
            hi = mid
        else:
            lo = mid
    return {"approximate_threshold": (lo+hi)/2, "slack_at_scan_c": slack(float(__import__("fractions").Fraction(data["c"]))),
            "note": "Numerical LP continuation of this selected pattern, using 2e-9 slack. Not a universal or exact threshold."}


def plot(summary, output):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    rows = summary["rows"]
    fig, axes = plt.subplots(2, 1, figsize=(10, 7), sharex=True)
    x = [r["c"] for r in rows]
    y = [r["objective"] for r in rows]
    axes[0].plot(x, y, "o-", ms=4, label="Incumbent count (lines guide the eye)")
    unfinished = [r for r in rows if r["status"] != 2]
    if unfinished:
        axes[0].scatter([r["c"] for r in unfinished], [r["bound"] for r in unfinished],
                        marker="v", color="tab:orange", label="Unfinished solver upper bound")
    axes[1].plot(x, [r.get("best_found_so_far", r["best_value"]) for r in rows], "o-", ms=4,
                 label="Best found iid lower bound (carried forward)")
    if any(r.get("best_found_so_far", r["best_value"])-r["best_value"] > 1e-10 for r in rows):
        axes[1].scatter(x, [r["best_value"] for r in rows], marker="x", color="gray",
                        label="Mass fit to this coefficient's MILP support")
    for ax in axes:
        for c, label in [(sqrt(2), r"$\sqrt{2}$"), (1.5213797068045676, r"$c_0$"),
                         ((1+sqrt(5))/2, r"$\varphi$")]:
            if not min(x)-.002 <= c <= max(x):
                continue
            ax.axvline(c, color="gray", ls="--", lw=1)
            ax.text(c+.002, .80, label, transform=ax.get_xaxis_transform(), va="top")
        ax.grid(alpha=.2)
        ax.legend(loc="upper left")
    axes[0].set_ylabel("Distinct-index count (denominator 660)")
    axes[1].set_ylabel("Actual iid probability")
    axes[1].set_xlabel("c")
    axes[0].set_title("Two against one: m=12 scan (fixed positive margin)")
    fig.tight_layout()
    fig.savefig(output, dpi=170)
    fig.savefig(output.with_suffix(".pdf"))


def main():
    from fractions import Fraction
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("directory", type=Path)
    p.add_argument("--plot-only", action="store_true")
    p.add_argument("--extra", nargs="*", type=Path, default=[])
    p.add_argument("--c-min", type=float, default=1)
    p.add_argument("--c-max", type=float, default=2)
    args = p.parse_args()
    summary_path = args.directory/"summary.json"
    if args.plot_only:
        plot(json.loads(summary_path.read_text()), args.directory/"scan.png")
        return
    candidates = [json.loads(path.read_text()) for directory in [args.directory]+args.extra
                  for path in directory.glob("m*.json")]
    unique = {}
    for d in candidates:
        key = Fraction(d["c"])
        if not args.c_min <= float(key) <= args.c_max:
            continue
        if key not in unique or (d["status"] == 2 and unique[key]["status"] != 2):
            unique[key] = d
    data = list(unique.values())
    data.sort(key=lambda d: Fraction(d["c"]))
    rows = []
    last_count = None
    best_found, best_source = 0., None
    for d in data:
        row = {k: d.get(k) for k in ["objective", "bound", "status", "best_value", "runtime", "margin"]}
        row["c"] = float(Fraction(d["c"]))
        row["c_exact"] = d["c"]
        if d["best_value"] > best_found:
            best_found, best_source = d["best_value"], row["c"]
        row["best_found_so_far"] = best_found
        row["best_bound_source_c"] = best_source
        if last_count is not None and d["objective"] != last_count:
            row["pattern_continuation"] = pattern_threshold(d)
        last_count = d["objective"]
        rows.append(row)
        print(json.dumps(row), flush=True)
    summary_path.write_text(json.dumps({"rows": rows}, indent=2)+"\n")


if __name__ == "__main__":
    main()
