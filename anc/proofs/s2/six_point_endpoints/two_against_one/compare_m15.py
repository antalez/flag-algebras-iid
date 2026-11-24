"""Check m=12 transition brackets at m=15 using lifted warm starts."""
import argparse
from fractions import Fraction as Q
from itertools import combinations_with_replacement
import json
from pathlib import Path

from search import solve, tuples


def lifted_start(source, c, margin, previous=None):
    """Add three copies to a 12-point witness, trying every support choice."""
    base = source["x"]
    support = sorted(set(base))
    ts, _, _ = tuples(15, "distinct")

    def score(xs):
        return sum(float(c)*xs[k]-xs[i]-xs[j] >= margin for i, j, k in ts)

    candidates = [sorted(base+list(extra))
                  for extra in combinations_with_replacement(support, 3)]
    if previous is not None:
        candidates.append(previous)
    best = max(candidates, key=score)
    return best, score(best)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=20)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--c-min", type=float, default=1)
    p.add_argument("--c-max", type=float, default=2)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    sources = [json.loads(path.read_text()) for path in args.source.glob("m12*.json")]
    sources = sorted((d for d in sources if args.c_min <= float(Q(d["c"])) <= args.c_max),
                     key=lambda d: Q(d["c"]))
    previous = None
    for source in sources:
        c, margin = Q(source["c"]), source["margin"]
        warm, warm_score = lifted_start(source, c, margin, previous)
        result = solve(15, c, "distinct", args.seconds, margin, args.seed, warm)
        result.update(warm_start_score=warm_score, m12_objective=source["objective"],
                      source_directory=str(args.source))
        if "x" in result:
            previous = result["x"]
        path = args.output/f"m15_c{c.numerator}_{c.denominator}_distinct_s{args.seed}.json"
        path.write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({k: result.get(k) for k in ["c", "m12_objective", "warm_start_score", "objective", "bound", "status", "runtime"]}), flush=True)


if __name__ == "__main__":
    main()
