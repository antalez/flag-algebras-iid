"""Order-six flag SDP for exact finite pattern covers.

Uses an exactly certified complete pattern cover. Rational PSD factors give
an exact universal upper bound even if the numerical SDP has not converged.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
import math
import os
from pathlib import Path
import sys
import time
from types import SimpleNamespace

for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(name, "2")

import numpy as np
from scipy import sparse
import clarabel

from enumerate_patterns import candidates, verify_cover


def unpack(vector, pairs, dim):
    """Convert sqrt(2)-scaled svec coordinates to a symmetric matrix."""
    result = np.zeros((dim, dim))
    for value, (i, j) in zip(vector, pairs):
        result[i, j] = result[j, i] = value if i == j else value / math.sqrt(2)
    return result


def certify(patterns, blocks, matrices, digits):
    """Round PSD factors to rationals and evaluate the resulting bound."""
    denominator = 10**digits
    common = math.lcm(60, *(block['norm'] for block in blocks)) * denominator**2
    numerators = [sum(v == 1 for v in pattern) * (common//60) for pattern in patterns]
    certificate = dict(s=6, blocks=[])
    for block, matrix in zip(blocks, matrices):
        eigenvalues, vectors = np.linalg.eigh((matrix+matrix.T)/2)
        factor = vectors * np.sqrt(np.maximum(eigenvalues, 0))
        integer_factor = [[int(round(float(value)*denominator)) for value in row]
                          for row in factor]
        gram = [[sum(a*b for a, b in zip(left, right)) for right in integer_factor]
                for left in integer_factor]
        coefficients = [gram[i][j] * (1 if i == j else 2) for i, j in block['pairs']]
        counts = block['counts']
        multiplier = common // (block['norm'] * denominator**2)
        for column in range(len(patterns)):
            total = sum(int(counts.data[k]) * coefficients[counts.indices[k]]
                        for k in range(counts.indptr[column], counts.indptr[column+1]))
            numerators[column] += multiplier * total
        certificate['blocks'].append(dict(t=block['t'], f=block['f'], type=block['type'],
                                          flags=block['flags'],
                                          L=[[str(Fraction(v, denominator)) for v in row]
                                             for row in integer_factor]))
    return Fraction(max(numerators), common), certificate


def assemble(data, block_specs=((2, 4), (3, 4), (4, 5))):
    n = data["size"]
    if n != 6:
        raise ValueError("This driver currently implements order six")
    ts = [tuple(t) for t in data["tuples"]]
    lookup = {t: j for j, t in enumerate(ts)}
    patterns = np.array([[1 if c == "+" else -1 for c in p] for p in data["patterns"]], dtype=np.int8)
    bits = (patterns == 1).astype(np.int64)
    cache = {}

    def codes(vertices):
        if vertices not in cache:
            local = candidates(len(vertices), data["c2_regression"], data.get("summands", 3))
            indices = [lookup[tuple(vertices[i] for i in t)] for t in local]
            cache[vertices] = bits[:, indices] @ (1 << np.arange(len(indices), dtype=np.int64))
        return cache[vertices]

    blocks = []
    for t, f in block_specs:
        marks = list(combinations(range(f), t))
        marks_index = {q: j for j, q in enumerate(marks)}
        records = defaultdict(list)
        norm = math.comb(n, t)*math.comb(n-t, f-t)*math.comb(n-f, f-t)
        for roots in combinations(range(n), t):
            root_codes = codes(roots)
            rest = tuple(i for i in range(n) if i not in roots)
            for left in combinations(rest, f-t):
                a = tuple(sorted(roots+left))
                a_marks = marks_index[tuple(a.index(i) for i in roots)]
                a_codes = codes(a)*len(marks)+a_marks
                for right in combinations(tuple(i for i in rest if i not in left), f-t):
                    b = tuple(sorted(roots+right))
                    b_marks = marks_index[tuple(b.index(i) for i in roots)]
                    b_codes = codes(b)*len(marks)+b_marks
                    for sigma in np.unique(root_codes):
                        selected = np.flatnonzero(root_codes == sigma)
                        records[int(sigma)].append((selected, a_codes[selected], b_codes[selected]))
        for sigma, pieces in sorted(records.items()):
            columns = np.concatenate([v[0] for v in pieces])
            lefts = np.concatenate([v[1] for v in pieces])
            rights = np.concatenate([v[2] for v in pieces])
            keys = np.union1d(lefts, rights)
            a, b = np.searchsorted(keys, lefts), np.searchsorted(keys, rights)
            keep = a <= b
            dim = len(keys)
            pairs = [(i, j) for j in range(dim) for i in range(j+1)]
            counts = sparse.coo_matrix((np.ones(sum(keep), dtype=np.int64),
                                       (b[keep]*(b[keep]+1)//2+a[keep], columns[keep])),
                                      shape=(len(pairs), len(patterns))).tocsc()
            flag_width = len(candidates(f, data["c2_regression"], data.get("summands", 3)))
            flags = []
            for key in keys:
                code, mark = divmod(int(key), len(marks))
                flags.append((tuple(1 if code & (1 << i) else -1 for i in range(flag_width)), marks[mark]))
            root_width = len(candidates(t, data["c2_regression"], data.get("summands", 3)))
            root_type = [1 if sigma & (1 << i) else -1 for i in range(root_width)] or None
            scale = np.array([1 if i == j else math.sqrt(2) for i, j in pairs])/norm
            operator = (sparse.diags(scale) @ counts).tocsc()
            blocks.append(dict(t=t, f=f, type=root_type, flags=flags, pairs=pairs,
                               norm=norm, counts=counts, operator=operator))
            print(f"Block ({t},{f}), type {root_type}: {dim} flags; {counts.nnz} entries", flush=True)
    arity = data.get("summands", 3)+1
    objective = (patterns == 1).sum(axis=1)/(arity*math.comb(n, arity))
    return patterns, objective, blocks


def fit(objective, blocks, selected, seconds, tolerance):
    c = objective[selected]
    n = len(selected)
    operators = [b["operator"][:, selected] for b in blocks]
    a = sparse.vstack([sparse.csc_matrix(np.ones((1, n))), -sparse.eye(n, format="csc")]
                      + [-op for op in operators], format="csc")
    rhs = np.zeros(a.shape[0])
    rhs[0] = 1
    cones = [clarabel.ZeroConeT(1), clarabel.NonnegativeConeT(n)]
    cones += [clarabel.PSDTriangleConeT(len(b["flags"])) for b in blocks]
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.max_threads = 2
    settings.time_limit = seconds
    settings.max_iter = 150
    settings.tol_gap_abs = settings.tol_gap_rel = settings.tol_feas = tolerance
    solver = clarabel.DefaultSolver(sparse.csc_matrix((n, n)), -c, a, rhs, cones, settings)
    result = solver.solve()
    matrices, offset = [], 1+n
    for b in blocks:
        length = len(b["pairs"])
        matrices.append(unpack(result.z[offset:offset+length], b["pairs"], len(b["flags"])))
        offset += length
    return dict(status=str(result.status), seconds=result.solve_time,
                primal=float(c @ np.array(result.x)), dual=float(result.z[0]),
                primal_residual=result.r_prim, dual_residual=result.r_dual), matrices, np.array(result.x)


def scores(objective, blocks, matrices):
    result = objective.copy()
    for b, q in zip(blocks, matrices):
        result += b["operator"].T @ np.array([q[i, j]*(1 if i == j else math.sqrt(2)) for i, j in b["pairs"]])
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover", type=Path, required=True)
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=120)
    p.add_argument("--rounds", type=int, default=8)
    p.add_argument("--initial", type=int, default=500)
    p.add_argument("--add", type=int, default=500)
    p.add_argument("--tolerance", type=float, default=1e-8)
    p.add_argument("--small-blocks", action="store_true")
    args = p.parse_args()
    data = json.loads(args.cover.read_text())
    verify_cover(data)
    tick = time.monotonic()
    patterns, objective, blocks = assemble(data, ((2, 4), (3, 4)) if args.small_blocks else ((2, 4), (3, 4), (4, 5)))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    active = set(np.argsort(objective)[-args.initial:].tolist())
    active.update(np.random.default_rng(42).choice(len(patterns), min(args.initial, len(patterns)), replace=False).tolist())
    history, best, best_certificate = [], float("inf"), None
    for iteration in range(args.rounds):
        selected = np.array(sorted(active))
        info, matrices, weights = fit(objective, blocks, selected, args.seconds, args.tolerance)
        values = scores(objective, blocks, matrices)
        # Replacing numerical Q by rational L L^T makes PSD exact.
        bound, certificate = certify(patterns.tolist(), blocks, matrices, 10)
        certificate.update(coefficient=data["coefficient"], tuples=data["tuples"],
                           exact_bound=str(bound), cover=str(args.cover))
        info.update(round=iteration+1, active=len(active), cover_patterns=len(patterns),
                    numerical_full_max=float(max(values)), exact_bound=str(bound),
                    exact_bound_decimal=float(bound))
        history.append(info)
        print(json.dumps(info), flush=True)
        if bound < best:
            best, best_certificate = bound, certificate
            (args.output_dir / "certificate.json").write_text(json.dumps(certificate, separators=(",", ":"))+"\n")
        np.savez_compressed(args.output_dir / "primal.npz", indices=selected, weights=weights)
        report = dict(coefficient=data["coefficient"], cover=str(args.cover),
                      patterns=len(patterns), dimensions=[len(b["flags"]) for b in blocks],
                      exact_bound=str(best), exact_bound_decimal=float(best),
                      below_half=best < .5, history=history, seconds=time.monotonic()-tick)
        (args.output_dir / "report.json").write_text(json.dumps(report, indent=2)+"\n")
        if best < .5:
            break
        violations = np.flatnonzero(values > info["dual"]+2e-7)
        new = set(violations[np.argsort(values[violations])[-args.add:]].tolist())-active
        if not new:
            break
        active.update(new)


if __name__ == "__main__":
    main()
