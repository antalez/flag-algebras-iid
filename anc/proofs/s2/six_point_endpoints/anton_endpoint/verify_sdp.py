"""Independent integer evaluation of a flag certificate on the exact cover.

Does not use flag_sdp.assemble, its sparse matrices, or any SDP solver.
Only the pattern-cover arithmetic is shared with the enumerator.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb, lcm
from pathlib import Path

from enumerate_patterns import candidates, verify_cover


def verify(cover, certificate):
    verify_cover(cover)
    if (certificate.get("summands", 3) != cover.get("summands", 3)
        or certificate["coefficient"] != cover["coefficient"] or certificate["tuples"] != cover["tuples"]):
        raise ValueError("Coefficient/tuple mismatch")
    n = cover["size"]
    if certificate["s"] != n:
        raise ValueError("Size mismatch")
    lookup = {tuple(t): i for i, t in enumerate(cover["tuples"])}

    def restriction(vertices):
        return tuple(lookup[tuple(vertices[i] for i in t)]
                     for t in candidates(len(vertices), cover["c2_regression"], cover.get("summands", 3)))

    blocks = []
    arity = cover.get("summands", 3)+1
    objective_denominator = arity*comb(n, arity)
    common = objective_denominator
    for block in certificate["blocks"]:
        t, f = block["t"], block["f"]
        if not 0 <= t < f <= n or 2*f-t > n:
            raise ValueError("Invalid flag dimensions")
        flags = {(tuple(s), tuple(r)): i for i, (s, r) in enumerate(block["flags"])}
        if len(flags) != len(block["flags"]):
            raise ValueError("Duplicate flag")
        factor = [[Fraction(v) for v in row] for row in block["L"]]
        if len(factor) != len(flags) or len({len(row) for row in factor}) > 1:
            raise ValueError("Invalid factor dimensions")
        denominator = lcm(*(v.denominator for row in factor for v in row))
        integer_factor = [[int(v*denominator) for v in row] for row in factor]
        gram = [[sum(a*b for a, b in zip(left, right)) for right in integer_factor]
                for left in integer_factor]
        norm = comb(n, t)*comb(n-t, f-t)*comb(n-f, f-t)
        common = lcm(common, norm*denominator**2)
        configs = []
        for roots in combinations(range(n), t):
            rest = tuple(i for i in range(n) if i not in roots)
            for a in combinations(rest, f-t):
                left = tuple(sorted(roots+a))
                for b in combinations(tuple(i for i in rest if i not in a), f-t):
                    right = tuple(sorted(roots+b))
                    configs.append((restriction(roots), restriction(left), tuple(left.index(i) for i in roots),
                                    restriction(right), tuple(right.index(i) for i in roots)))
        if len(configs) != norm:
            raise ValueError("Normalization error")
        blocks.append(dict(type=tuple(block["type"]) if block["type"] else (),
                           flags=flags, gram=gram, configurations=configs,
                           denominator=norm*denominator**2))
    best, worst = None, None
    for encoded in cover["patterns"]:
        pattern = tuple(1 if s == "+" else -1 for s in encoded)
        value = sum(s == 1 for s in pattern)*(common//objective_denominator)
        for block in blocks:
            total = 0
            for root, left, lm, right, rm in block["configurations"]:
                if tuple(pattern[i] for i in root) != block["type"]:
                    continue
                a = block["flags"].get((tuple(pattern[i] for i in left), lm))
                b = block["flags"].get((tuple(pattern[i] for i in right), rm))
                if a is not None and b is not None:
                    total += block["gram"][a][b]
            value += total*(common//block["denominator"])
        if best is None or value > best:
            best, worst = value, encoded
    bound = Fraction(best, common)
    if bound != Fraction(certificate["exact_bound"]):
        raise ValueError("Reported bound disagrees with independent evaluation")
    return dict(exact_bound=str(bound), decimal_bound=float(bound), below_half=bound < Fraction(1, 2),
                patterns_checked=len(cover["patterns"]), pruning_certificates_checked=len(cover["pruned"]),
                worst_pattern=worst, coefficient=cover["coefficient"], independent_evaluation=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover", type=Path, required=True)
    p.add_argument("--certificate", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = verify(json.loads(args.cover.read_text()), json.loads(args.certificate.read_text()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
