"""Complete seven-point outer cover from exact six-point compatibility.

Adapted from Anton/enumerate_seven.py: four states per four-set at this c.
No numerical geometry is used to exclude seven-point patterns.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import numpy as np

from enumerate_patterns import verify_cover


def enumerate_compatible(data, max_leaves=2000000, seconds=300):
    verify_cover(data)
    lookup = {tuple(t): i for i, t in enumerate(data["tuples"])}
    four6, four7 = list(combinations(range(6), 4)), list(combinations(range(7), 4))
    states6 = []
    for pattern in data["patterns"]:
        values = []
        for four in four6:
            signs = [pattern[lookup[tuple(i for i in four if i != ell)+(ell,)]] for ell in four[1:]]
            if signs not in (["-", "-", "-"], ["-", "-", "+"], ["-", "+", "+"], ["+", "+", "+"]):
                raise ValueError("The covering catalog contains a nonmonotone four-set")
            values.append(signs.count("+"))
        states6.append(values)
    masks = [[0]*4 for _ in four6]
    for row, pattern in enumerate(states6):
        for j, value in enumerate(pattern):
            masks[j][value] |= 1 << row
    index = {q: i for i, q in enumerate(four7)}
    subsets = list(combinations(range(7), 6))
    scopes = [[index[tuple(s[i] for i in four)] for four in four6] for s in subsets]
    members = [[] for _ in four7]
    for constraint, scope in enumerate(scopes):
        for local, variable in enumerate(scope):
            members[variable].append((constraint, local))
    full = (1 << len(states6))-1
    leaves, restrictions = [], []
    nodes = rejected = 0
    tick, next_report = time.monotonic(), 20

    def search(domains, remaining, values):
        nonlocal nodes, rejected, next_report
        nodes += 1
        if nodes % 4096 == 0:
            elapsed = time.monotonic()-tick
            if elapsed > seconds:
                raise TimeoutError("Seven-point cover time limit")
            if elapsed >= next_report:
                print(f"{elapsed:.1f}s: nodes={nodes}, seven-point patterns={len(leaves)}", flush=True)
                next_report = elapsed+20
        domains, remaining, values = list(domains), list(remaining), list(values)
        while remaining:
            best, options, forced = None, None, False
            for variable in remaining:
                choices = [state for state in range(4)
                           if all(domains[c] & masks[j][state] for c, j in members[variable])]
                if not choices:
                    rejected += 1
                    return
                if len(choices) == 1:
                    state = choices[0]
                    values[variable] = state
                    remaining.remove(variable)
                    for c, j in members[variable]:
                        domains[c] &= masks[j][state]
                    forced = True
                    break
                if options is None or len(choices) < len(options):
                    best, options = variable, choices
            if forced:
                continue
            remaining.remove(best)
            for state in options:
                child = domains.copy()
                for c, j in members[best]:
                    child[c] &= masks[j][state]
                values[best] = state
                search(child, remaining, values)
            return
        if not all(d and d & (d-1) == 0 for d in domains):
            raise ValueError("Ambiguous restriction")
        leaves.append(bytes(values))
        restrictions.append(tuple(d.bit_length()-1 for d in domains))
        if len(leaves) >= max_leaves:
            raise TimeoutError("Seven-point cover size limit")

    complete, stop_reason = True, None
    try:
        search([full]*7, list(range(35)), [-1]*35)
    except TimeoutError as exc:
        complete, stop_reason = False, str(exc)
    states = np.frombuffer(b"".join(leaves), dtype=np.uint8).reshape(-1, 35).copy()
    restrictions = np.array(restrictions, dtype=np.uint16)
    return states, restrictions, np.array(states6, dtype=np.uint8), {
        "patterns": len(leaves), "nodes": nodes, "rejected": rejected,
        "seconds": time.monotonic()-tick, "complete": complete, "stop_reason": stop_reason,
        "coefficient": data["coefficient"],
        "meaning": "Outer cover by complete six-point compatibility; global realizability is not asserted.",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--max-leaves", type=int, default=2000000)
    args = p.parse_args()
    data = json.loads(args.cover.read_text())
    states, restrictions, states6, report = enumerate_compatible(data, args.max_leaves, args.seconds)
    report["six_cover"] = str(args.cover)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(args.output, states=states, restrictions=restrictions, states6=states6)
    args.output.with_suffix(".json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
