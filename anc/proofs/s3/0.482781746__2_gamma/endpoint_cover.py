"""Exact four-point cover at c=(1+sqrt(13))/2."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from algebraic_field import make_field, solve
sys.path.pop(0)
from verify import forms

POLYNOMIAL = [-3, -1, 1]
ROOT_INTERVAL = (2, 3)
Endpoint = make_field(POLYNOMIAL, root_interval=ROOT_INTERVAL)
C = Endpoint([0, 1])
CUTS = sorted({C / 2, C - 1, C / (C - 1), C})


def rows(n, cuts):
    result = []
    for kind, vertices, target in forms(n, cuts):
        row = [Endpoint(0)] * n
        if kind == "pair":
            row[vertices[1]] = Endpoint(1)
            row[vertices[0]] = -cuts[target]
        else:
            for vertex in vertices:
                row[vertex] = Endpoint(1)
            row[vertices[target]] -= C + 1
        result.append([sum(row[j:], Endpoint(0)) for j in range(n)])
    return result


def verify_cover(cover):
    assert cover["polynomial"] == POLYNOMIAL and cover["root_interval"] == list(ROOT_INTERVAL)
    assert cover["c"] == C.json()
    n = cover["n"]
    assert n in (4, 5)
    cuts = list(map(Endpoint, cover["cuts"]))
    assert cuts == sorted(set(cuts)) and all(q > 1 for q in cuts)
    rr = rows(n, cuts)
    width, intervals = len(rr), []

    def interval(prefix):
        assert len(prefix) <= width and set(prefix) <= {"+", "-"}
        start = int("".join("1" if s == "+" else "0" for s in prefix) or "0", 2)
        shift = width - len(prefix)
        return start << shift, (start + 1) << shift

    for prefix, proof in cover["pruned"].items():
        weights = {int(i): Endpoint(v) for i, v in proof.items()}
        assert weights and all(0 <= i < len(prefix) and w > 0 for i, w in weights.items())
        assert all(sum((w * (1 if prefix[i] == "+" else -1) * rr[i][j]
                        for i, w in weights.items()), Endpoint(0)) >= 0 for j in range(n))
        intervals.append(interval(prefix))
    for pattern in cover["patterns"]:
        assert len(pattern) == width
        intervals.append(interval(pattern))
    end = 0
    for lo, hi in sorted(intervals):
        assert lo == end, "Gap or overlap in exact endpoint cover"
        end = hi
    assert end == 1 << width
    return n, cuts


def generate(n=4, cuts=CUTS):
    import numpy as np
    from scipy.optimize import linprog
    rr = rows(n, cuts)
    array = np.array([[float(x) for x in row] for row in rr])
    scales = np.maximum(np.max(np.abs(array), axis=1), 1)
    array /= scales[:, None]
    cover = dict(n=n, polynomial=POLYNOMIAL, root_interval=list(ROOT_INTERVAL), c=C.json(),
                 cuts=[q.json() for q in cuts], patterns=[], pruned={})
    started = last = time.monotonic()
    calls = 0

    def exclusion(signs):
        h = array[:len(signs)] * np.array(signs)[:, None]
        lp = linprog(np.zeros(len(signs)), A_ub=-h.T, b_ub=np.zeros(n),
                     A_eq=np.ones((1, len(signs))), b_eq=[1], bounds=(0, None), method="highs")
        if not lp.success:
            return None
        active = [i for i, w in enumerate(lp.x) if w > 1e-9]
        if not active:
            return None
        # LP used normalized rows; convert proposed weights to original rows.
        proposal = [float(lp.x[i]) / scales[i] for i in active]
        total = sum(proposal)
        proposal = [x / total for x in proposal]
        signed = [[signs[i] * x for x in rr[i]] for i in active]
        slack = np.array([[float(x) for x in row] for row in signed]).T @ proposal
        zeros = [j for j in range(n) if abs(slack[j]) < 1e-7]
        matrix = [[row[j] for row in signed] for j in zeros] + [[Endpoint(1)] * len(active)]
        weights = solve(Endpoint, matrix, [0] * len(zeros) + [1],
                        free=[Q(x).limit_denominator(10 ** 6) for x in proposal])
        if weights is None or not all(w > 0 for w in weights):
            return None
        if not all(sum((w * row[j] for w, row in zip(weights, signed)), Endpoint(0)) >= 0
                   for j in range(n)):
            return None
        return {str(i): w.json() for i, w in zip(active, weights)}

    def dfs(signs, witness=None):
        nonlocal calls, last
        if witness is None or (signs and signs[-1] * array[len(signs) - 1] @ witness >= -1e-10):
            h = array[:len(signs)] * np.array(signs)[:, None]
            matrix = np.vstack([np.c_[h, np.ones(len(signs))], np.c_[-np.eye(n), np.ones(n)]])
            lp = linprog([0] * n + [-1], A_ub=matrix, b_ub=np.zeros(len(matrix)),
                         A_eq=[[1] * n + [0]], b_eq=[1], bounds=[(0, 1)] * (n + 1), method="highs")
            calls += 1
            if not lp.success or lp.x[-1] < 1e-8:
                proof = exclusion(signs)
                if proof is not None:
                    cover["pruned"]["".join("+" if x == 1 else "-" for x in signs)] = proof
                    return
                witness = None
            else:
                witness = lp.x[:-1]
        if len(signs) == len(rr):
            cover["patterns"].append("".join("+" if x == 1 else "-" for x in signs))
            return
        if time.monotonic() - last > 20:
            print(json.dumps(dict(phase="endpoint_cover", patterns=len(cover["patterns"]),
                                 exclusions=len(cover["pruned"]), lp_calls=calls)), flush=True)
            last = time.monotonic()
        dfs(signs + [1], witness)
        dfs(signs + [-1], witness)

    dfs([])
    verify_cover(cover)
    print(json.dumps(dict(phase="endpoint_covered", patterns=len(cover["patterns"]),
                         exclusions=len(cover["pruned"]), seconds=time.monotonic() - started)), flush=True)
    return cover


if __name__ == "__main__":
    path = HERE / "endpoint_n4_cover.json"
    if path.exists():
        cover = json.loads(path.read_text())
        verify_cover(cover)
    else:
        cover = generate()
        path.write_text(json.dumps(cover, separators=(",", ":")) + "\n")
    print(json.dumps(dict(patterns=len(cover["patterns"]), exclusions=len(cover["pruned"]),
                         exact_cover_verified=True)), flush=True)
