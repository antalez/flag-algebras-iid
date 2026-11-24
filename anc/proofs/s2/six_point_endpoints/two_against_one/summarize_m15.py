"""Compare the m=15 incumbent/bound intervals across m=12 transitions."""
import argparse
from fractions import Fraction as Q
import json
from math import ceil
from pathlib import Path

from analyze_scan import pattern_threshold


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("directory", type=Path)
    p.add_argument("--monotone", action="store_true",
                   help="Combine bounds across c using monotonicity of the same fixed-margin problem")
    p.add_argument("--fallback", type=Path,
                   help="Use previous results for cases whose longer rerun is not yet saved")
    args = p.parse_args()
    paths = list(args.fallback.glob("m15*.json")) if args.fallback else []
    paths += list(args.directory.glob("m15*.json"))
    by_c = {}
    for path in paths:
        item = json.loads(path.read_text())
        by_c[Q(item["c"])] = item
    data = list(by_c.values())
    data.sort(key=lambda d: Q(d["c"]))
    assert data and len(data) % 2 == 0, "Require paired endpoints for each transition"
    assert len({(d["m"], d["mode"], d["margin"]) for d in data}) == 1
    lower = [d["objective"] for d in data]
    upper = [ceil(d["bound"]-1e-7) for d in data]
    if args.monotone:
        for i in range(1, len(data)):
            lower[i] = max(lower[i], lower[i-1])
        for i in range(len(data)-2, -1, -1):
            upper[i] = min(upper[i], upper[i+1])
    assert all(a <= b for a, b in zip(lower, upper))
    rows = []
    for index in range(0, len(data), 2):
        below, above = data[index:index+2]
        low_upper, high_upper = upper[index:index+2]
        row = {"c_below": below["c"], "c_above": above["c"],
               "m12_counts": [below["m12_objective"], above["m12_objective"]],
               "m15_below_interval": [lower[index], low_upper],
               "m15_above_interval": [lower[index+1], high_upper],
               "solver_optimal": [below["status"] == 2, above["status"] == 2],
               "optimal_from_combined_bounds": [lower[index] == low_upper, lower[index+1] == high_upper],
               "incumbent_increase": above["objective"]-below["objective"],
               "fixed_margin_increase_proved_by_solver_bounds": lower[index+1] > low_upper,
               "above_pattern_continuation": pattern_threshold(above)}
        rows.append(row)
        print(json.dumps(row), flush=True)
    out = {"m": 15, "denominator": 1365, "pairs": rows, "monotonicity_used": args.monotone,
           "interpretation": "Incumbents are exactly checked witnesses. Bounds concern the fixed-margin MILP only; continuation thresholds are numerical."}
    (args.directory/"comparison.json").write_text(json.dumps(out, indent=2)+"\n")


if __name__ == "__main__":
    main()
