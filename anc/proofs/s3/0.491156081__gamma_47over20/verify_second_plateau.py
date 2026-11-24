"""Standard-library exact verification of the candidate second S3 plateau certificate."""

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
from pathlib import Path

from second_endpoint_cover import C, verify_cover as verify_algebraic_cover
from second_plateau_field import Value, B, Z, A, D, POLYNOMIAL, ROOT_INTERVAL, positive_definite
from verify import forms, verify_cover as verify_rational_cover

HERE = Path(__file__).resolve().parent


def verify(cover, certificate, progress=False):
    mode = certificate["mode"]
    if mode == "interior":
        verify_rational_cover(cover)
        n, cuts = cover["n"], list(map(Q,cover["cuts"]))
        c = Q(cover["c"])
        assert c == Q(47,20)
        assert certificate["c"] == cover["c"]
        interval = "(1+sqrt(13))/2<c<=47/20"
    else:
        assert mode == "endpoint"
        n, cuts = verify_algebraic_cover(cover)
        c = C
        assert certificate["c"] == C.json()
        interval = "(1+sqrt(13))/2<c<=root(c^3-c^2-2c-3)"
    assert n == certificate["n"] == 4 and certificate["cuts"] == cover["cuts"]
    assert certificate["value_polynomial"] == POLYNOMIAL
    assert certificate["value_root_interval"] == list(ROOT_INTERVAL)
    assert 2<c<3 and c*c-c-3>0
    assert 0<Z<1 and A>0 and D>0 and Z+A+D==1
    numerator = (A*(Z**3+3*Z**2*(A+D)+3*Z*(A**2+2*A*D))
                 +D*(Z**3+3*Z**2*(A+D)+3*Z*(A+D)**2+A**3))
    assert B == numerator/(1-Z**4)
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
        if progress:
            print(json.dumps(dict(phase="exact_psd", type=root_type, dimension=len(Y))), flush=True)
        WY = [[sum((a * b for a, b in zip(row, column) if a and b), Value(0))
               for column in zip(*Y)] for row in W]
        gram = [[sum((a * b for a, b in zip(row, other) if a and b), Value(0))
                 for other in W] for row in WY]
        blocks.append((block, gram, {flag: i for i, flag in enumerate(flags)}))
    scores = []
    for pattern_index, pattern in enumerate(cover["patterns"]):
        if progress and pattern_index % 100 == 0:
            print(json.dumps(dict(phase="exact_scores", checked=pattern_index)), flush=True)
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
        endpoint_decimal=float(c),
        bound=B.json(), bound_decimal=float(B), tight_patterns=sum(score == B for score in scores),
        interval=interval, near_optimality_constraints_used=False,
        psd_verification="rational LDL with exact algebraic entry enclosures",
        exact_plateau_proved=True, all_exact_checks_passed=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", default="second_plateau_n4_field_certificate.json")
    parser.add_argument("--progress", action="store_true")
    args = parser.parse_args()
    certificate = json.loads((HERE / args.certificate).read_text())
    stem = Path(args.certificate).name
    for suffix in ("_field_candidate.json", "_field_certificate.json"):
        if stem.endswith(suffix):
            stem = stem[:-len(suffix)]
            break
    else:
        raise ValueError("Certificate filename must end with _field_candidate.json or _field_certificate.json")
    if certificate["mode"] == "interior":
        cover_path = HERE / "n4_c47-20_cuts47-40_60-47_27-20_47-27_47-20_cover.json"
    else:
        cover_path = HERE / (stem + "_cover.json")
    cover = json.loads(cover_path.read_text())
    result = verify(cover, certificate, progress=args.progress)
    (HERE / (stem + "_verification.json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
