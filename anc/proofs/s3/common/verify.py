"""Standard-library verification of rational colored S3 upper certificates."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
import json
from math import comb, lcm


def forms(n, cuts):
    return (
        [("pair", (i, j), q) for i, j in combinations(range(n), 2)
         for q in range(len(cuts))]
        + [("sum", vertices, target) for vertices in combinations(range(n), 4)
           for target in (1, 2, 3)]
    )


def gap_rows(n, c, cuts):
    result = []
    for kind, vertices, target in forms(n, cuts):
        row = [Q(0)] * n
        if kind == "pair":
            row[vertices[1]] = 1
            row[vertices[0]] = -cuts[target]
        else:
            for vertex in vertices:
                row[vertex] = 1
            # Start with all four points, then subtract (c+1)*target.
            row[vertices[target]] -= c + 1
        gaps = [sum(row[j:]) for j in range(n)]
        denominator = lcm(*(value.denominator for value in gaps))
        result.append([int(value * denominator) for value in gaps])
    return result


def verify_cover(cover):
    n = cover["n"]
    assert isinstance(n, int) and 4 <= n <= 6
    c = Q(cover["c"])
    cuts = list(map(Q, cover["cuts"]))
    assert 0 < c < 3 and cuts == sorted(set(cuts)) and all(q > 1 for q in cuts)
    rows = gap_rows(n, c, cuts)
    width = len(rows)
    intervals = []

    def interval(prefix):
        assert len(prefix) <= width and set(prefix) <= {"+", "-"}
        start = int("".join("1" if s == "+" else "0" for s in prefix) or "0", 2)
        shift = width - len(prefix)
        return start << shift, (start + 1) << shift

    for prefix, proof in cover["pruned"].items():
        weights = {int(key): Q(value) for key, value in proof.items()}
        assert weights and all(value > 0 for value in weights.values())
        assert all(0 <= key < len(prefix) for key in weights)
        assert all(
            sum(value * (1 if prefix[key] == "+" else -1) * rows[key][j]
                for key, value in weights.items()) >= 0
            for j in range(n)
        )
        intervals.append(interval(prefix))
    for pattern in cover["patterns"]:
        assert len(pattern) == width
        intervals.append(interval(pattern))
    end = 0
    for left, right in sorted(intervals):
        assert left == end, "Gap or overlap in complete sign cover"
        end = right
    assert end == 1 << width
    return n, c, cuts


def verify(cover, cert):
    n, c, cuts = verify_cover(cover)
    assert cert["n"] == n and Q(cert["c"]) == c
    assert list(map(Q, cert["cuts"])) == cuts
    ff = forms(n, cuts)
    lookup = {form: index for index, form in enumerate(ff)}
    blocks = []
    seen = set()
    for block in cert["blocks"]:
        t, f = block["t"], block["f"]
        assert isinstance(t, int) and isinstance(f, int)
        assert 0 <= t < f < n and 2 * f - t <= n
        assert (t, f, block["type"]) not in seen
        seen.add((t, f, block["type"]))
        assert 0 <= block["type"] < 1 << len(forms(t, cuts))
        flags = block["flags"]
        assert len(flags) == len(set(flags))
        assert all(isinstance(flag, int) and
                   0 <= flag < (1 << len(forms(f, cuts))) * comb(f, t)
                   for flag in flags)
        factor, denominator = block["factor"], block["denominator"]
        assert isinstance(denominator, int) and denominator > 0
        assert len(factor) == len(flags) and factor
        assert len({len(row) for row in factor}) == 1
        assert all(isinstance(value, int) for row in factor for value in row)
        gram = [[sum(a * b for a, b in zip(x, y)) for y in factor] for x in factor]
        blocks.append((block, gram, {flag: i for i, flag in enumerate(flags)}))
    scores = []
    for pattern in cover["patterns"]:
        cache = {}

        def code(vertices):
            if vertices not in cache:
                cache[vertices] = sum(
                    1 << bit for bit, (kind, local, target) in enumerate(forms(len(vertices), cuts))
                    if pattern[lookup[kind, tuple(vertices[i] for i in local), target]] == "+"
                )
            return cache[vertices]

        score = Q(sum(pattern[i] == "+" for i, form in enumerate(ff) if form[0] == "sum"),
                  4 * comb(n, 4))
        for block, gram, indices in blocks:
            t, f = block["t"], block["f"]
            marks = list(combinations(range(f), t))
            counts = Counter()
            for roots in combinations(range(n), t):
                if code(roots) != block["type"]:
                    continue
                rest = tuple(i for i in range(n) if i not in roots)
                for extension in combinations(rest, f - t):
                    a = tuple(sorted(roots + extension))
                    fa = code(a) * len(marks) + marks.index(tuple(a.index(i) for i in roots))
                    for other in combinations(tuple(i for i in rest if i not in extension), f - t):
                        b = tuple(sorted(roots + other))
                        fb = code(b) * len(marks) + marks.index(tuple(b.index(i) for i in roots))
                        if fa in indices and fb in indices:
                            counts[indices[fa], indices[fb]] += 1
            numerator = sum(count * gram[i][j] for (i, j), count in counts.items())
            norm = comb(n, t) * comb(n - t, f - t) * comb(n - f, f - t)
            score += Q(numerator, norm * block["denominator"] ** 2)
        scores.append(score)
    bound = max(scores)
    if "bound" in cert:
        assert Q(cert["bound"]) == bound
    return dict(
        c=str(c), n=n, cuts=list(map(str, cuts)),
        patterns=len(scores), exclusions=len(cover["pruned"]),
        blocks=[len(block["flags"]) for block in cert["blocks"]],
        bound=str(bound), upper_decimal=float(bound), exact_checks_passed=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("cover")
    parser.add_argument("certificate")
    args = parser.parse_args()
    with open(args.cover) as stream:
        cover = json.load(stream)
    with open(args.certificate) as stream:
        certificate = json.load(stream)
    print(json.dumps(verify(cover, certificate), indent=2))
