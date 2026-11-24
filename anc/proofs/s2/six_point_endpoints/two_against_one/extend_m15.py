"""Longer m=15 reruns, retaining earlier witnesses and solver bounds."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from search import solve


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--side", choices=["below", "above"], required=True)
    p.add_argument("--seconds", type=float, default=180)
    p.add_argument("--c", nargs="+", help="Optionally rerun only these exact coefficients")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    files = sorted(args.source.glob("m15*.json"),
                   key=lambda path: Q(json.loads(path.read_text())["c"]))
    assert len(files) == 16
    selected = files[::2] if args.side == "below" else files[1::2]
    if args.c:
        requested = set(map(Q, args.c))
        selected = [path for path in selected if Q(json.loads(path.read_text())["c"]) in requested]
        assert len(selected) == len(requested)
    for path in reversed(selected):
        old = json.loads(path.read_text())
        target = args.output/path.name
        if target.exists():
            saved = json.loads(target.read_text())
            if saved["status"] == 2 or saved.get("extended_time_limit", 0) >= args.seconds:
                print(f"Already finished: {target.name}", flush=True)
                continue
            old = saved
        if old["status"] == 2:
            old["reused_optimal_source"] = str(path)
            target.write_text(json.dumps(old, indent=2)+"\n")
            print(f"Reused optimum: c={old['c']}, count={old['objective']}", flush=True)
            continue
        print(json.dumps({"type": "starting", "c": old["c"],
                          "prior_incumbent": old["objective"], "prior_bound": old["bound"],
                          "time_limit": args.seconds}), flush=True)
        new = solve(old["m"], Q(old["c"]), old["mode"], args.seconds,
                    old["margin"], old["seed"], old["x"], progress=True)
        # Same fixed-margin problem: bounds from either solve remain valid.
        result = dict(new if new.get("objective", -1) >= old["objective"] else old)
        bound = min(old["bound"], new["bound"])
        result.update(bound=bound, status=2 if bound < result["objective"]+1-1e-6 else new["status"],
                      m12_objective=old["m12_objective"], source_result=str(path),
                      prior_objective=old["objective"], prior_bound=old["bound"],
                      new_run_bound=new["bound"], new_run_status=new["status"],
                      new_run_runtime=new["runtime"], extended_time_limit=args.seconds)
        target.write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({"type": "completed", **{k: result[k] for k in
                         ["c", "objective", "bound", "status", "new_run_runtime"]}}), flush=True)


if __name__ == "__main__":
    main()
