"""Seven-point flag certificates for P(X1+X2 < c X3).

The six-point cover is the exact object produced by ``sdp6.py``.  This
driver builds the outer seven-point cover obtained by requiring every
six-point restriction to occur in that cover, then fits the inherited
six-point flag blocks together with the new (t,f)=(1,4) block.

The seven-point cover is deliberately an outer cover: compatibility of all
six-point restrictions is necessary, but is not claimed to be sufficient for
realizability by seven ordered gaps.  That direction is enough for an upper
bound.  Numerical factors are rounded and checked by integer arithmetic.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
import math
import os
from pathlib import Path
import sys
import time

for _thread_variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_thread_variable, '2')

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "anton_endpoint"))
from enumerate_patterns import candidates, verify_cover, gap_rows
from quadratic import Q2
from flag_sdp import assemble, scores, certify, sparse, unpack
import clarabel


def four_state_catalog(data):
    """Return the local four-set states and the state array for each 6-pattern."""
    n = data["size"]
    if n != 6 or data.get("summands", 3) != 2:
        raise ValueError("Expected a complete two-against-one six-point cover")
    tuples = [tuple(t) for t in data["tuples"]]
    lookup = {t: i for i, t in enumerate(tuples)}
    local_tuples = candidates(4, data["c2_regression"], 2)
    fours = list(combinations(range(6), 4))
    state_lookup, states = {}, []
    states6 = []
    for pattern in data["patterns"]:
        row = []
        for four in fours:
            signature = tuple(1 if pattern[lookup[tuple(four[i] for i in t)]] == "+" else -1
                              for t in local_tuples)
            if signature not in state_lookup:
                state_lookup[signature] = len(states)
                states.append(signature)
            row.append(state_lookup[signature])
        states6.append(row)
    return np.array(states, dtype=np.int8), np.array(states6, dtype=np.uint8), fours


def global_event_signs(data, states):
    """Recover the 70 distinct-index comparisons from four-set signatures."""
    catalog = four_state_catalog(data)[0]
    fours = list(combinations(range(7), 4))
    local = {t: i for i, t in enumerate(candidates(4, False, 2))}
    columns = []
    for event in candidates(7, False, 2):
        scope = next(i for i, four in enumerate(fours) if set(event) <= set(four))
        positions = tuple(fours[scope].index(v) for v in event)
        columns.append(catalog[states[:, scope], local[positions]])
    return np.array(columns, dtype=np.int8).T


def verify_seven_exclusions(data):
    """Check exact Farkas contradictions for excluded global sign patterns."""
    exclusions = data.get('seven_exclusions', {})
    if not isinstance(exclusions, dict):
        raise ValueError('Invalid seven-point exclusions')
    rows = gap_rows(7, candidates(7, False, 2), Q2(*data['coefficient']))
    for pattern, encoded in exclusions.items():
        if len(pattern) != len(rows) or set(pattern)-{'+', '-'}:
            raise ValueError('Invalid excluded seven-point pattern')
        weights = {int(i): Q2(*v) for i, v in encoded.items()}
        if (not weights or any(i < 0 or i >= len(rows) for i in weights)
                or any(w.sign() < 0 for w in weights.values()) or not any(weights.values())):
            raise ValueError('Invalid seven-point Farkas weights')
        for j in range(7):
            if sum(w*(1 if pattern[i] == '+' else -1)*rows[i][j]
                   for i, w in weights.items()).sign() < 0:
                raise ValueError('Invalid exact seven-point exclusion')
    return set(exclusions)


def enumerate_seven(data, seconds=300, max_leaves=2_000_000):
    """Enumerate seven-point assignments compatible with every six-cover row."""
    verify_cover(data)
    local_states, states6, fours6 = four_state_catalog(data)
    state_count = len(local_states)
    fours7 = list(combinations(range(7), 4))
    sixes7 = list(combinations(range(7), 6))
    index7 = {q: i for i, q in enumerate(fours7)}
    # For each omitted vertex, map its 15 local four-sets to global variables.
    scopes = [[index7[tuple(s[i] for i in four)] for four in fours6]
              for s in sixes7]

    masks = [[0] * state_count for _ in fours6]
    for row_index, row in enumerate(states6):
        for j, state in enumerate(row):
            masks[j][int(state)] |= 1 << row_index
    full = (1 << len(states6)) - 1
    members = [[] for _ in fours7]
    for constraint, scope in enumerate(scopes):
        for local, variable in enumerate(scope):
            members[variable].append((constraint, local))

    leaves, restrictions = [], []
    nodes = rejected = 0
    tick, next_report = time.monotonic(), 20

    def search(domains, remaining, values):
        nonlocal nodes, rejected, next_report
        nodes += 1
        if nodes % 4096 == 0:
            elapsed = time.monotonic() - tick
            if elapsed > seconds:
                raise TimeoutError("seven-point cover time limit")
            if elapsed >= next_report:
                print(f"{elapsed:.1f}s: nodes={nodes}, patterns={len(leaves)}", flush=True)
                next_report = elapsed + 20
        domains, remaining, values = list(domains), list(remaining), list(values)
        while remaining:
            best = options = None
            forced = False
            for variable in remaining:
                choices = [state for state in range(state_count)
                           if all(domains[c] & masks[j][state]
                                  for c, j in members[variable])]
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
        if not all(domain and domain & (domain - 1) == 0 for domain in domains):
            raise ValueError("Ambiguous six-point restriction")
        leaves.append(bytes(values))
        restrictions.append(tuple(domain.bit_length() - 1 for domain in domains))
        # The public limit concerns retained rows. Before exact filtering,
        # at most one raw leaf per supplied global exclusion is extra.
        if len(leaves) >= max_leaves+len(data.get('seven_exclusions', {})):
            raise TimeoutError("seven-point cover size limit")

    complete, stop_reason = True, None
    try:
        search([full] * 7, list(range(35)), [-1] * 35)
    except TimeoutError as exc:
        complete, stop_reason = False, str(exc)
    states = np.frombuffer(b"".join(leaves), dtype=np.uint8).reshape(-1, 35).copy()
    restrictions = np.array(restrictions, dtype=np.uint16)
    excluded = verify_seven_exclusions(data)
    removed = 0
    if excluded:
        signatures = [''.join('+' if v == 1 else '-' for v in row)
                      for row in global_event_signs(data, states)]
        if complete and not excluded <= set(signatures):
            raise ValueError('Excluded pattern absent from compatible cover')
        keep = np.array([signature not in excluded for signature in signatures])
        removed = int(np.count_nonzero(~keep))
        states, restrictions = states[keep], restrictions[keep]
    report = dict(patterns=len(leaves), states=state_count, nodes=nodes,
                  rejected=rejected, seconds=time.monotonic() - tick,
                  complete=complete, stop_reason=stop_reason,
                  coefficient=data["coefficient"], six_cover=None,
                  meaning="Outer cover by complete six-point compatibility")
    if excluded:
        report.update(patterns=len(states), global_exclusions=removed,
                      meaning='Six-point compatibility with exact global seven-point Farkas exclusions')
    return states, restrictions, states6, report


def root_configurations():
    """Ordered disjoint extensions; interchanging them also occurs in this list."""
    configurations = []
    fours = list(combinations(range(7), 4))
    lookup = {v: i for i, v in enumerate(fours)}
    for root in range(7):
        rest = tuple(i for i in range(7) if i != root)
        for left_extra in combinations(rest, 3):
            left = tuple(sorted((root,) + left_extra))
            right = tuple(sorted((root,) + tuple(i for i in rest if i not in left_extra)))
            configurations.append((lookup[left], lookup[right], left.index(root), right.index(root)))
    assert len(configurations) == 140
    return configurations


def root_block(states, state_count):
    """Store one orientation per off-diagonal pair, as in the six-point blocks."""
    pairs = [(i, j) for j in range(state_count * 4) for i in range(j + 1)]
    columns, indices = [], []
    for left, right, lm, rm in root_configurations():
        a = states[:, left].astype(np.int64) * 4 + lm
        b = states[:, right].astype(np.int64) * 4 + rm
        keep = a <= b
        columns.append(np.flatnonzero(keep))
        indices.append((b[keep] * (b[keep] + 1) // 2 + a[keep]))
    columns, indices = np.concatenate(columns), np.concatenate(indices)
    counts = sparse.coo_matrix((np.ones(len(columns), dtype=np.int64), (indices, columns)),
                               shape=(len(pairs), len(states))).tocsc()
    scale = np.array([1 if i == j else math.sqrt(2) for i, j in pairs]) / 140
    return dict(t=1, f=4, type=None, flags=list(range(state_count * 4)), pairs=pairs,
                norm=140, counts=sparse.csc_matrix(counts),
                operator=(sparse.diags(scale) @ counts).tocsc())


def root_scores(states, q, state_count):
    integral = q.dtype == object or np.issubdtype(q.dtype, np.integer)
    # Python integers keep exact Gram evaluations safe from int64 overflow.
    q = q.astype(object) if integral else q
    values = np.zeros(len(states), dtype=object if integral else float)
    for left, right, lm, rm in root_configurations():
        a = states[:, left].astype(np.int64) * 4 + lm
        b = states[:, right].astype(np.int64) * 4 + rm
        values += q[a, b]
    return values if integral else values / 140


def realizable_anchors(data, states, count=100, seed=9173):
    """Return cover rows produced by random strict seven-point samples."""
    if count == 0:
        return set()
    local_states, _, _ = four_state_catalog(data)
    local_lookup = {tuple(int(v) for v in row): i for i, row in enumerate(local_states)}
    row_lookup = {tuple(int(v) for v in row): i for i, row in enumerate(states)}
    local_events = candidates(4, data["c2_regression"], 2)
    fours = list(combinations(range(7), 4))
    coefficient = float(Fraction(data["coefficient"][0]))
    rng = np.random.default_rng(seed)
    anchors = set()
    for _ in range(max(1, count) * 20):
        x = np.sort(rng.exponential(size=7))
        row = []
        for four in fours:
            signature = tuple(1 if sum(x[four[i]] for i in t[:-1]) < coefficient * x[four[t[-1]]]
                              else -1 for t in local_events)
            row.append(local_lookup[signature])
        index = row_lookup.get(tuple(row))
        if index is not None:
            anchors.add(index)
        if len(anchors) >= count:
            break
    return anchors


def restricted_blocks(blocks, states, restrictions, state_count):
    n = len(states)
    averaging = sparse.coo_matrix((np.full(7 * n, 1 / 7),
        (restrictions.ravel(), np.repeat(np.arange(n), 7))),
        shape=(blocks[0]["operator"].shape[1], n)).tocsc()
    inherited = [dict(b, operator=(b["operator"] @ averaging).tocsc()) for b in blocks]
    return inherited + [root_block(states, state_count)]


def fit7(objective, blocks, selected, seconds, tolerance, verbose=False,
         chordal=False, moment_slack=0., threads=2):
    """Clarabel fit with a longer iteration budget for the 64-flag root block."""
    c = objective[selected]
    n = len(selected)
    operators = [b["operator"][:, selected] for b in blocks]
    a = sparse.vstack([sparse.csc_matrix(np.ones((1, n))),
                       -sparse.eye(n, format="csc")] + [-op for op in operators], format="csc")
    rhs = np.zeros(a.shape[0])
    rhs[0] = 1
    cones = [clarabel.ZeroConeT(1), clarabel.NonnegativeConeT(n)]
    cones += [clarabel.PSDTriangleConeT(len(b["flags"])) for b in blocks]
    offset = 1+n
    for block in blocks:
        for j, (a_, b_) in enumerate(block['pairs']):
            if a_ == b_:
                rhs[offset+j] = moment_slack
        offset += len(block['pairs'])
    settings = clarabel.DefaultSettings()
    settings.verbose = verbose
    settings.max_threads = threads
    settings.time_limit = seconds
    settings.max_iter = 1000
    settings.tol_gap_abs = settings.tol_gap_rel = settings.tol_feas = tolerance
    settings.tol_ktratio = max(1e-5, tolerance * 100)
    # Avoid a chordal-merge panic observed on small active subsets in 0.11.1.
    settings.chordal_decomposition_enable = chordal
    if chordal:
        settings.chordal_decomposition_merge_method = 'parent_child'
    solver = clarabel.DefaultSolver(sparse.csc_matrix((n, n)), -c, a, rhs, cones, settings)
    result = solver.solve()
    matrices, offset = [], 1 + n
    for b in blocks:
        length = len(b["pairs"])
        matrices.append(unpack(result.z[offset:offset + length], b["pairs"], len(b["flags"])))
        offset += length
    info = dict(status=str(result.status), seconds=result.solve_time,
                primal=float(c @ np.array(result.x)), dual=float(result.z[0]),
                primal_residual=result.r_prim, dual_residual=result.r_dual)
    info['regularized_dual'] = info['dual'] + moment_slack*sum(float(np.trace(q)) for q in matrices)
    return info, matrices, np.array(result.x)


def exact_certificate(patterns, blocks, matrices, states, restrictions, state_count, digits=6,
                      return_values=False):
    """Round and evaluate the inherited plus root blocks using integers."""
    _, inherited = certify(patterns.tolist(), blocks, matrices[:-1], digits)
    six_den = 3 * math.comb(6, 3)
    common6 = math.lcm(six_den, *(b["norm"] for b in blocks)) * 10**(2 * digits)
    values6 = [int(sum(v == 1 for v in row)) * (common6 // six_den) for row in patterns]
    d = 10**digits
    for b, saved in zip(blocks, inherited["blocks"]):
        factor = [[int(Fraction(v) * d) for v in row] for row in saved["L"]]
        gram = [[sum(a * b_ for a, b_ in zip(l, r)) for r in factor] for l in factor]
        coeff = [gram[i][j] * (1 if i == j else 2) for i, j in b["pairs"]]
        multiplier = common6 // (b["norm"] * d * d)
        for j in range(len(patterns)):
            values6[j] += multiplier * sum(int(b["counts"].data[k]) * coeff[b["counts"].indices[k]]
                                            for k in range(b["counts"].indptr[j], b["counts"].indptr[j + 1]))
    q = matrices[-1]
    eig, vectors = np.linalg.eigh((q + q.T) / 2)
    factor = [[int(round(v * d)) for v in row]
              for row in vectors * np.sqrt(np.maximum(eig, 0))]
    gram = np.array([[sum(a * b for a, b in zip(l, r)) for r in factor] for l in factor], dtype=object)
    common = math.lcm(7 * common6, 140 * d * d)
    values = np.array(values6, dtype=object)[restrictions].sum(axis=1) * (common // (7 * common6))
    values += root_scores(states, gram, state_count) * (common // (140 * d * d))
    maximum = max(values)
    bound = Fraction(int(maximum), common)
    cert = dict(s=7, format_version=2, inherited=inherited, root_factor=factor,
                       root_denominator=d, root_state_count=state_count,
                       exact_bound=str(bound), worst_pattern=int(np.argmax(values)))
    return (bound, cert, values, common) if return_values else (bound, cert)


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary=path.with_name(path.name+'.tmp')
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def minimax_blend(reference, candidate):
    """Minimize the full-cover maximum along a convex segment of certificates."""
    delta = candidate-reference
    lo, hi = 0., 1.
    for _ in range(60):
        middle = (lo+hi)/2
        worst = int(np.argmax(reference+middle*delta))
        if delta[worst] < 0:
            lo = middle
        else:
            hi = middle
    choices = [0., 1., (lo+hi)/2]
    return min(choices, key=lambda alpha: float(np.max(reference+alpha*delta)))


def certificate_matrices(certificate):
    matrices = []
    for block in certificate['inherited']['blocks']:
        factor = np.array([[float(Fraction(v)) for v in row] for row in block['L']])
        matrices.append(factor @ factor.T)
    factor = np.array(certificate['root_factor'], dtype=float)/certificate['root_denominator']
    return matrices+[factor @ factor.T]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover6", type=Path, required=True)
    p.add_argument("--cover7", type=Path, required=True,
                   help="NPZ output; its sidecar JSON is written automatically")
    p.add_argument("--seed-certificate", type=Path,
                   help="Existing six-point certificate used to initialize the SDP")
    p.add_argument("--phase", choices=("cover", "solve", "all"), default="all")
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--cover-seconds", type=float, default=300)
    p.add_argument("--seconds", type=float, default=90)
    p.add_argument("--rounds", type=int, default=8)
    p.add_argument("--initial", type=int, default=500)
    p.add_argument("--add", type=int, default=300)
    p.add_argument("--tolerance", type=float, default=1e-7)
    p.add_argument("--anchors", type=int, default=100)
    p.add_argument("--small-blocks", action="store_true",
                   help="Use only inherited (2,4),(3,4) blocks plus the 7-point (1,4) block")
    p.add_argument('--full', action='store_true', help='Fit all seven-point rows directly')
    p.add_argument('--seed-ray', action='store_true',
                   help='Optimize one nonnegative scale on inherited seed matrices and the full root block')
    p.add_argument('--seed-block-scales', action='store_true',
                   help='Optimize a separate nonnegative scale per inherited seed block plus the root block')
    p.add_argument('--verbose', action='store_true', help='Print Clarabel iteration diagnostics')
    p.add_argument('--chordal', action='store_true',
                   help='Use chordal decomposition with the parent_child merge method')
    p.add_argument('--moment-slack', type=float, default=0.,
                   help='Add epsilon I to primal PSD moments (dual trace regularization)')
    p.add_argument('--start-certificate', type=Path,
                   help='Verified version-2 seven-point certificate for baseline and row selection')
    p.add_argument('--start-primal', type=Path,
                   help='Prior primal.npz whose largest weights guide initial row selection')
    p.add_argument('--threads', type=int, default=8, help='Clarabel linear-algebra threads')
    p.add_argument('--digits', type=int, default=10, help='Decimal precision of rational PSD factors')
    p.add_argument("--max-leaves", type=int, default=2_000_000)
    args = p.parse_args()
    configuration = dict(full=args.full, small_blocks=args.small_blocks,
                         seed_ray=args.seed_ray, seed_block_scales=args.seed_block_scales,
                         chordal=args.chordal, moment_slack=args.moment_slack,
                         threads=args.threads, digits=args.digits,
                         start_certificate=str(args.start_certificate) if args.start_certificate else None,
                         start_primal=str(args.start_primal) if args.start_primal else None,
                         seconds_per_round=args.seconds, tolerance=args.tolerance,
                         cover6=str(args.cover6), cover7=str(args.cover7),
                         seed_certificate=str(args.seed_certificate) if args.seed_certificate else None)
    if min(args.cover_seconds, args.seconds, args.rounds, args.initial, args.add,
           args.tolerance, args.max_leaves, args.threads, args.digits) <= 0 or args.anchors < 0 or args.moment_slack < 0:
        p.error('Limits must be positive and anchors nonnegative')
    data = json.loads(args.cover6.read_text())
    verify_cover(data)
    if args.phase in ("cover", "all"):
        states, restrictions, states6, report = enumerate_seven(data, args.cover_seconds, args.max_leaves)
        report["six_cover"] = str(args.cover6)
        args.cover7.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.cover7, states=states, restrictions=restrictions, states6=states6)
        save(args.cover7.with_suffix(".json"), report)
    if args.phase == "cover":
        return
    meta = json.loads(args.cover7.with_suffix(".json").read_text())
    if not meta["complete"] or meta['coefficient'] != data['coefficient']:
        raise ValueError("Incomplete seven-point cover; no upper bound can be certified")
    archive = np.load(args.cover7)
    states, restrictions, states6 = archive["states"], archive["restrictions"], archive["states6"]
    # A complete sidecar alone does not establish coverage. Re-enumerate the
    # deterministic compatibility tree and compare every archived row.
    check_states, check_restrictions, check_six, checked_cover = enumerate_seven(
        data, args.cover_seconds, args.max_leaves)
    if (not checked_cover['complete'] or not np.array_equal(states, check_states)
            or not np.array_equal(restrictions, check_restrictions)
            or not np.array_equal(states6, check_six)):
        raise ValueError('Seven-point archive failed complete re-enumeration')
    block_specs = ((2, 4), (3, 4)) if args.small_blocks else ((2, 4), (3, 4), (4, 5))
    patterns, objective, blocks = assemble(data, block_specs)
    state_count = int(max(states.max(initial=0), states6.max(initial=0)) + 1)
    seed = json.loads(args.seed_certificate.read_text()) if args.seed_certificate else None
    if (args.seed_ray or args.seed_block_scales) and not seed:
        p.error('Seed scaling requires --seed-certificate')
    matrices = []
    if seed:
        if (seed.get('s') != 6 or seed.get('summands') != 2
                or seed['coefficient'] != data['coefficient']
                or seed['tuples'] != data['tuples'] or len(seed['blocks']) < len(blocks)):
            raise ValueError('Seed coefficient/tuple/block mismatch')
        # Do not trust its claimed six-point bound: the lifted rational factors
        # are checked independently on every seven-point row below.
        for b, sb in zip(blocks, seed["blocks"]):
            if json.loads(json.dumps(b['flags'])) != sb['flags']:
                raise ValueError('Seed flag basis mismatch')
            factor = np.array([[float(Fraction(v)) for v in row] for row in sb["L"]])
            matrices.append(factor @ factor.T)
    else:
        matrices = [np.zeros((len(b["flags"]), len(b["flags"]))) for b in blocks]
    objective7 = objective[restrictions].mean(axis=1)
    # The seed contains only the inherited six-point blocks; the new root
    # block is initialized at zero until the first seven-point fit.
    values = scores(objective, blocks, matrices)[restrictions].mean(axis=1)
    seed_matrices = [q.copy() for q in matrices]
    seed_correction = values - objective7
    seed_corrections = []
    if args.seed_block_scales:
        for block, q in zip(blocks, seed_matrices):
            coeff = np.array([q[i,j]*(1 if i == j else math.sqrt(2)) for i,j in block['pairs']])
            seed_corrections.append((block['operator'].T @ coeff)[restrictions].mean(axis=1))
    from verify_sdp7 import verify as verify7
    start_certificate = None
    if args.start_certificate:
        start_certificate = json.loads(args.start_certificate.read_text())
        verify7(data, states, restrictions, start_certificate)
        start_blocks = start_certificate['inherited']['blocks']
        if (len(start_blocks) != len(blocks)
                or any(json.loads(json.dumps(b['flags'])) != sb['flags']
                       for b,sb in zip(blocks,start_blocks))):
            raise ValueError('Starting certificate flag basis mismatch')
        start_matrices = []
        for sb in start_blocks:
            factor = np.array([[float(Fraction(v)) for v in row] for row in sb['L']])
            start_matrices.append(factor @ factor.T)
        factor = np.array(start_certificate['root_factor'], dtype=float)/start_certificate['root_denominator']
        values = scores(objective, blocks, start_matrices)[restrictions].mean(axis=1)
        values += root_scores(states, factor @ factor.T, state_count)
    active = set(np.argsort(values)[-args.initial:].tolist())
    active.update(np.random.default_rng(42).choice(len(states), min(args.initial, len(states)), replace=False).tolist())
    active.update(realizable_anchors(data, states, args.anchors))
    if args.start_primal:
        with np.load(args.start_primal) as saved:
            indices, weights = saved['indices'], saved['weights']
            if (indices.shape != weights.shape or indices.ndim != 1
                    or np.any(indices < 0) or np.any(indices >= len(states))
                    or not np.isfinite(weights).all()):
                raise ValueError('Invalid starting primal support')
            active.update(indices[np.argsort(weights)[-args.initial:]].tolist())
    # Almost-constant positive iid laws have no successful events. Their row
    # is a feasible moment distribution and prevents artificial infeasibility
    # of a restricted master problem. Anchors alone need not provide one.
    local_catalog, _, _ = four_state_catalog(data)
    empty_state = next(i for i, row in enumerate(local_catalog) if np.all(row == -1))
    active.update(np.flatnonzero(np.all(states == empty_state, axis=1)).tolist())
    if args.full:
        active = set(range(len(states)))
    best, history = None, []
    args.output_dir.mkdir(parents=True, exist_ok=True)

    existing_path = args.output_dir/'certificate.json'
    if existing_path.exists():
        existing = json.loads(existing_path.read_text())
        verify7(data, states, restrictions, existing)
        best = Fraction(existing['exact_bound'])

    def accept(bound, certificate):
        nonlocal best_matrices
        certificate.update(coefficient=data['coefficient'], summands=2, tuples=data['tuples'],
                           cover6=str(args.cover6), cover7=str(args.cover7),
                           configuration=configuration)
        result = verify7(data, states, restrictions, certificate)
        result['complete_cover_reenumerated'] = True
        result['coverage'] = checked_cover['meaning']+'; complete cover re-enumerated'
        save(args.output_dir/'certificate.json', certificate)
        save(args.output_dir/'verification.json', result)
        best_matrices = certificate_matrices(certificate)

    best_matrices = certificate_matrices(existing) if existing_path.exists() else None

    if start_certificate:
        starting_bound = Fraction(start_certificate['exact_bound'])
        if best is None or starting_bound < best:
            accept(starting_bound, start_certificate)
            best = starting_bound

    # Lift the seed with a zero root block. It supplies a valid baseline even
    # when a numerical round fails or its full-cover separation is poor.
    if seed:
        baseline_matrices = matrices + [np.zeros((4*state_count, 4*state_count))]
        seed_bound, baseline = exact_certificate(patterns, blocks, baseline_matrices,
                                                 states, restrictions, state_count, digits=10)
        if best is None or seed_bound < best:
            accept(seed_bound, baseline)
            best = seed_bound
        print(json.dumps(dict(baseline_exact=str(best), baseline_decimal=float(best))), flush=True)
    for iteration in range(args.rounds):
        selected = np.array(sorted(active))
        if args.seed_ray or args.seed_block_scales:
            # Each inherited matrix stays PSD under a common nonnegative scale.
            # The scalar moment is their summed correction, valid in expectation.
            corrections = seed_corrections if args.seed_block_scales else [seed_correction]
            scalars = [dict(t=0, f=0, flags=[0], pairs=[(0, 0)],
                            operator=sparse.csc_matrix(correction[selected][None, :]))
                       for correction in corrections]
            local_blocks = scalars + [root_block(states[selected], state_count)]
        else:
            local_blocks = restricted_blocks(blocks, states[selected], restrictions[selected], state_count)
        info, matrices, weights = fit7(objective7[selected], local_blocks, np.arange(len(selected)),
                                       args.seconds, args.tolerance, args.verbose,
                                       args.chordal, args.moment_slack, args.threads)
        if args.seed_ray or args.seed_block_scales:
            alphas = [max(0., float(q[0, 0])) for q in matrices[:-1]]
            info['seed_scales'] = alphas
            if not args.seed_block_scales:
                alphas *= len(seed_matrices)
            matrices = [alpha*q for alpha,q in zip(alphas,seed_matrices)] + [matrices[-1]]
        if (info['status'] not in ('Solved', 'AlmostSolved', 'MaxTime', 'MaxIterations')
                or not all(np.isfinite(q).all() for q in matrices)):
            info.update(round=iteration+1, active=len(active), accepted=False)
            history.append(info)
            save(args.output_dir/'report.json', dict(patterns=len(states), history=history,
                 configuration=configuration,
                 exact_bound=str(best) if best is not None else None))
            raise RuntimeError(f"Seven-point fit failed: {info['status']}; preserved verified baseline")
        values = scores(objective, blocks, matrices[:-1])[restrictions].mean(axis=1) + root_scores(states, matrices[-1], state_count)
        bound, certificate = exact_certificate(patterns, blocks, matrices, states, restrictions,
                                               state_count, digits=args.digits)
        save(args.output_dir/'last_candidate.json', dict(certificate,
             coefficient=data['coefficient'], summands=2, tuples=data['tuples']))
        if best_matrices is not None:
            reference = scores(objective, blocks, best_matrices[:-1])[restrictions].mean(axis=1)
            reference += root_scores(states, best_matrices[-1], state_count)
            # Factor rounding projects the new matrices to PSD before mixing.
            candidate_matrices = certificate_matrices(certificate)
            candidate_values = scores(objective, blocks, candidate_matrices[:-1])[restrictions].mean(axis=1)
            candidate_values += root_scores(states, candidate_matrices[-1], state_count)
            alpha = minimax_blend(reference, candidate_values)
            info['blend_fraction'] = alpha
            if 0 < alpha < 1:
                blend = [(1-alpha)*a+alpha*b for a,b in zip(best_matrices,candidate_matrices)]
                blended_bound, blended_certificate = exact_certificate(patterns, blocks, blend, states,
                                                                         restrictions, state_count,
                                                                         digits=args.digits)
                if blended_bound < bound:
                    bound, certificate = blended_bound, blended_certificate
        certificate.update(coefficient=data["coefficient"], summands=2, tuples=data["tuples"],
                           cover6=str(args.cover6), cover7=str(args.cover7))
        info.update(round=iteration + 1, active=len(active), full_max=float(max(values)),
                    exact_bound=str(bound), exact_bound_decimal=float(bound))
        history.append(info)
        print(json.dumps(info), flush=True)
        if best is None or bound < best:
            accept(bound, certificate)
            best = bound
        np.savez_compressed(args.output_dir / "primal.npz", indices=selected, weights=weights)
        save(args.output_dir / "report.json", dict(patterns=len(states), exact_bound=str(best),
             exact_bound_decimal=float(best), configuration=configuration, history=history))
        violations = np.flatnonzero(values > info["dual"] + 1e-6)
        violations = np.array([i for i in violations if int(i) not in active],dtype=np.int64)
        if not len(violations):
            break
        new = set(violations[np.argsort(values[violations])[-args.add:]].tolist()) - active
        if not new:
            break
        active.update(new)


if __name__ == "__main__":
    main()
