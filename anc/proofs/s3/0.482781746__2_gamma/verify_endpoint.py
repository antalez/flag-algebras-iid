"""Standard-library exact verification of the first S3 plateau certificate."""

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
from math import comb

from endpoint_cover import C, HERE, verify_cover
from endpoint_field import Value, B, Z, positive_definite
from verify import forms

VALUE_POLYNOMIAL = [4, -4, -3, -6, 3]
VALUE_ROOT_INTERVAL = (2, 3)
ENDPOINT_POLYNOMIAL = [-3, -1, 1]
INTERVAL = "2<c<=(1+sqrt(13))/2"


def check_lower_value():
    assert 0 < Z < 1 and 4 * Z ** 4 - 4 * Z ** 3 - 3 * Z ** 2 - 6 * Z + 3 == 0
    assert B == ((1 - Z) - (1 - Z) ** 4) / (1 - Z ** 4)


def verify(cover, certificate):
    n, cuts = verify_cover(cover)
    assert certificate["n"] == n and certificate["c"] == C.json()
    assert certificate["cuts"] == cover["cuts"]
    assert certificate["value_polynomial"] == VALUE_POLYNOMIAL
    assert certificate["value_root_interval"] == list(VALUE_ROOT_INTERVAL)
    # This root supplies the optimal single-positive-atom lower family.
    check_lower_value()
    ff = forms(n, cuts)
    lookup = {form: i for i, form in enumerate(ff)}
    blocks, seen = [], set()
    for block in certificate["blocks"]:
        t, f, root_type = block["t"], block["f"], block["type"]
        assert isinstance(t, int) and isinstance(f, int) and isinstance(root_type, int)
        assert 0 <= t < f < n and 2 * f - t <= n
        assert 0 <= root_type < 1 << len(forms(t, cuts))
        assert (t, f, root_type) not in seen
        seen.add((t, f, root_type))
        flags = block["flags"]
        assert len(flags) == len(set(flags))
        assert all(isinstance(flag, int) and
                   0 <= flag < (1 << len(forms(f, cuts))) * comb(f, t) for flag in flags)
        W = [[Value(x) for x in row] for row in block["basis"]]
        Y = [[Value(x) for x in row] for row in block["matrix"]]
        assert len(W) == len(flags) and W and all(len(row) == len(Y) for row in W)
        positive_definite(Y)
        WY = [[sum((a * b for a, b in zip(row, column) if a and b), Value(0))
               for column in zip(*Y)] for row in W]
        gram = [[sum((a * b for a, b in zip(row, other) if a and b), Value(0))
                 for other in W] for row in WY]
        blocks.append((block, gram, {flag: i for i, flag in enumerate(flags)}))
    scores = []
    for pattern_index, pattern in enumerate(cover["patterns"]):
        cache = {}

        def code(vertices):
            if vertices not in cache:
                cache[vertices] = sum(
                    1 << bit for bit, (kind, local, target) in enumerate(forms(len(vertices), cuts))
                    if pattern[lookup[kind, tuple(vertices[i] for i in local), target]] == "+"
                )
            return cache[vertices]

        score = Value(Q(sum(pattern[i] == "+" for i, form in enumerate(ff) if form[0] == "sum"),
                        4 * comb(n, 4)))
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
            norm = comb(n, t) * comb(n - t, f - t) * comb(n - f, f - t)
            score += sum((count * gram[i][j] for (i, j), count in counts.items()), Value(0)) / norm
        scores.append(score)
    violations = [(i, float(score - B)) for i, score in enumerate(scores) if score > B]
    near_tight = [i for i, score in enumerate(scores) if -Q(1, 10 ** 7) < score - B < Q(1, 10 ** 7)]
    assert not violations, ("Scores exceed exact plateau value", violations[:30],
                            "near-tight patterns for reconstruction", near_tight)
    maximum = max(scores)
    assert maximum == B
    return dict(
        patterns=len(scores), exclusions=len(cover["pruned"]),
        original_dimensions=[len(b["basis"]) for b in certificate["blocks"]],
        reduced_dimensions=[len(b["matrix"]) for b in certificate["blocks"]],
        endpoint_polynomial=ENDPOINT_POLYNOMIAL, endpoint_decimal=float(C),
        bound=B.json(), bound_decimal=float(B), tight_patterns=sum(score == B for score in scores),
        interval=INTERVAL, near_optimality_constraints_used=False,
        exact_plateau_proved=True, all_exact_checks_passed=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", default="endpoint_n4_field_certificate.json")
    args = parser.parse_args()
    cover = json.loads((HERE / "endpoint_n4_cover.json").read_text())
    certificate = json.loads((HERE / args.certificate).read_text())
    result = verify(cover, certificate)
    (HERE / "endpoint_n4_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
