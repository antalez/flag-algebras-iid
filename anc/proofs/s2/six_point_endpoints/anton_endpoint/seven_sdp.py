"""Seven-point extension: inherited order-six flags plus (t,f)=(1,4).

Constraint generation separates over the entire six-compatible outer cover.
Exact rational Gram factors certify bounds regardless of numerical convergence.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path
import time

from flag_sdp import assemble, fit, scores, np, sparse, certify
from enumerate_patterns import verify_cover


def configurations():
    four = list(combinations(range(7), 4))
    lookup = {v: i for i, v in enumerate(four)}
    result = []
    for root in range(7):
        rest = tuple(i for i in range(7) if i != root)
        for a in combinations(rest, 3):
            left = tuple(sorted((root,)+a))
            right = tuple(sorted((root,)+tuple(i for i in rest if i not in a)))
            result.append((lookup[left], lookup[right], left.index(root), right.index(root)))
    assert len(result) == 140
    return result


def root_block(states):
    pairs = [(i, j) for j in range(16) for i in range(j+1)]
    counts = np.zeros((136, len(states)), dtype=np.int16)
    columns = np.arange(len(states))
    for left, right, lm, rm in configurations():
        a = 4*states[:, left].astype(np.int16)+lm
        b = 4*states[:, right].astype(np.int16)+rm
        keep = a <= b
        counts[b[keep]*(b[keep]+1)//2+a[keep], columns[keep]] += 1
    scale = np.array([1 if i == j else math.sqrt(2) for i, j in pairs])/140
    return dict(t=1, f=4, type=None, flags=list(range(16)), pairs=pairs, norm=140,
                counts=sparse.csc_matrix(counts), operator=sparse.csc_matrix(scale[:, None]*counts))


def root_scores(states, q):
    # For exact integers, check the entire accumulation against overflow.
    integral = q.dtype == object or np.issubdtype(q.dtype, np.integer)
    if integral:
        largest = max(abs(int(v)) for v in q.flat)
        dtype = np.int64 if 140*largest < 2**63 else object
        q = q.astype(dtype)
    else:
        dtype = float
    values = np.zeros(len(states), dtype=dtype)
    for left, right, lm, rm in configurations():
        values += q[4*states[:, left]+lm, 4*states[:, right]+rm]
    return values if integral else values/140


def restricted_blocks(blocks, states, restrictions):
    n = len(states)
    averaging = sparse.coo_matrix((np.full(7*n, 1/7),
        (restrictions.ravel(), np.repeat(np.arange(n), 7))),
        shape=(blocks[0]["operator"].shape[1], n)).tocsc()
    inherited = [dict(b, operator=(b["operator"] @ averaging).tocsc()) for b in blocks]
    return inherited+[root_block(states)]


def exact_certificate(patterns, blocks, matrices, states, restrictions, digits=6):
    _, inherited = certify(patterns.tolist(), blocks, matrices[:-1], digits)
    d = 10**digits
    common6 = math.lcm(60, *(b["norm"] for b in blocks))*d*d
    values6 = [int(sum(v == 1 for v in row))*(common6//60) for row in patterns]
    for b, saved in zip(blocks, inherited["blocks"]):
        factor = [[int(Fraction(v)*d) for v in row] for row in saved["L"]]
        gram = [[sum(a*b for a, b in zip(l, r)) for r in factor] for l in factor]
        coeff = [gram[i][j]*(1 if i == j else 2) for i, j in b["pairs"]]
        counts = b["counts"]
        multiplier = common6//(b["norm"]*d*d)
        for j in range(len(patterns)):
            values6[j] += multiplier*sum(int(counts.data[k])*coeff[counts.indices[k]]
                for k in range(counts.indptr[j], counts.indptr[j+1]))
    q = matrices[-1]
    eig, vectors = np.linalg.eigh((q+q.T)/2)
    factor = [[int(round(v*d)) for v in row] for row in vectors*np.sqrt(np.maximum(eig, 0))]
    gram = np.array([[sum(a*b for a, b in zip(l, r)) for r in factor] for l in factor], dtype=object)
    common = math.lcm(7*common6, 140*d*d)
    # Python integer arithmetic for the final weighted sums; root_scores may
    # safely use int64 internally when its explicit bound allows it.
    values = np.array(values6, dtype=object)[restrictions].sum(axis=1)*(common//(7*common6))
    values += root_scores(states, gram).astype(object)*(common//(140*d*d))
    maximum = max(values)
    bound = Fraction(int(maximum), common)
    cert = dict(s=7, inherited=inherited, root_factor=factor, root_denominator=d,
                root_flag_convention="4*number_of_successful_targets+root_position",
                exact_bound=str(bound), worst_pattern=int(np.argmax(values)))
    return bound, cert


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover6", type=Path, required=True)
    p.add_argument("--cover7", type=Path, required=True)
    p.add_argument("--seed-certificate", type=Path, required=True)
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--rounds", type=int, default=8)
    p.add_argument("--seconds", type=float, default=90)
    p.add_argument("--initial", type=int, default=500)
    p.add_argument("--add", type=int, default=300)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    verify_cover(data)
    meta = json.loads(args.cover7.with_suffix(".json").read_text())
    if not meta["complete"] or meta["coefficient"] != data["coefficient"]:
        raise ValueError("Incomplete/mismatched seven-point cover")
    archive = np.load(args.cover7)
    states, restrictions = archive["states"], archive["restrictions"]
    patterns, objective, blocks = assemble(data)
    seed = json.loads(args.seed_certificate.read_text())
    matrices = []
    for b, sb in zip(blocks, seed["blocks"]):
        if json.loads(json.dumps(b["flags"])) != sb["flags"]:
            raise ValueError("Seed flag basis differs")
        factor = np.array([[float(Fraction(v)) for v in row] for row in sb["L"]])
        matrices.append(factor @ factor.T)
    objective7 = objective[restrictions].mean(axis=1)
    values = scores(objective, blocks, matrices)[restrictions].mean(axis=1)
    active = set(np.argsort(values)[-args.initial:].tolist())
    active.update(np.random.default_rng(42).choice(len(states), args.initial, replace=False).tolist())
    best, history, tick = float("inf"), [], time.monotonic()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for iteration in range(args.rounds):
        selected = np.array(sorted(active))
        local_blocks = restricted_blocks(blocks, states[selected], restrictions[selected])
        info, matrices, weights = fit(objective7[selected], local_blocks, np.arange(len(selected)), args.seconds, 1e-8)
        values = scores(objective, blocks, matrices[:-1])[restrictions].mean(axis=1)+root_scores(states, matrices[-1])
        bound, cert = exact_certificate(patterns, blocks, matrices, states, restrictions)
        cert.update(coefficient=data["coefficient"], cover6=str(args.cover6), cover7=str(args.cover7))
        info.update(round=iteration+1, active=len(active), full_max=float(max(values)),
                    exact_bound=str(bound), exact_bound_decimal=float(bound))
        history.append(info)
        print(json.dumps(info), flush=True)
        if bound < best:
            best = bound
            (args.output_dir/"certificate.json").write_text(json.dumps(cert, separators=(",", ":"))+"\n")
        np.savez_compressed(args.output_dir/"primal.npz", indices=selected, weights=weights)
        report = dict(patterns=len(states), exact_bound=str(best), exact_bound_decimal=float(best),
                      below_half=best < .5, history=history, seconds=time.monotonic()-tick)
        (args.output_dir/"report.json").write_text(json.dumps(report, indent=2)+"\n")
        if best < .5:
            break
        violations = np.flatnonzero(values > info["dual"]+1e-6)
        new = set(violations[np.argsort(values[violations])[-args.add:]].tolist())-active
        if not new:
            break
        active.update(new)


if __name__ == "__main__":
    main()
