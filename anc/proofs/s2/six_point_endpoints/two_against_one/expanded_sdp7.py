"""Seven-point SDP with the additional (3,5) PSD family.

Convex eigenvector cuts enforce every matrix entry without a rank constraint.
Numerical duals are only proposals; rational Gram factors and a separate
exact verifier establish every saved upper bound. Checkpoints are resumable.
"""
import argparse
from fractions import Fraction as Q
from itertools import combinations
import hashlib
import json
from pathlib import Path
import time

from sdp7 import (np, sparse, assemble, root_block, global_event_signs, candidates,
                  enumerate_seven, unpack, certificate_matrices, exact_certificate, save)
from optimal_sdp7 import FeasibilityLP, IncrementalLP, moments
from verify_sdp7 import verify
from scipy.linalg import eigh


def packed_indices(block):
    if '_packed_indices' not in block:
        right, left = np.tril_indices(len(block['flags']))
        scale = np.where(left == right, 1., np.sqrt(2))
        block['_packed_indices'] = left, right, scale
    return block['_packed_indices']


def block_score(block, matrix):
    left, right, scale = packed_indices(block)
    return np.asarray(block['operator'].T @ (matrix[left, right]*scale)).ravel()


def block_moment(block, weights):
    left, right, scale = packed_indices(block)
    values = (block['operator'] @ weights)/scale
    matrix = np.zeros((len(block['flags']), len(block['flags'])))
    matrix[left, right] = values
    matrix[right, left] = values
    return matrix


def extra_blocks(data, states, five_roots=None):
    """Assemble (3,5), and optionally selected or all (5,6), products."""
    from math import comb
    signs = global_event_signs(data, states)
    lookup = {t: i for i, t in enumerate(candidates(7, False, 2))}
    cache = {}

    def codes(vertices):
        if vertices not in cache:
            ids = [lookup[tuple(vertices[i] for i in t)]
                   for t in candidates(len(vertices), False, 2)]
            cache[vertices] = (signs[:, ids] == 1).astype(np.int64) @ (
                1 << np.arange(len(ids), dtype=np.int64))
        return cache[vertices]

    blocks = []
    families = [(3, 5, None)]
    if five_roots is not None:
        families.append((5, 6, None if five_roots == 'all' else set(five_roots)))
    for t, f, selected_roots in families:
        marks = list(combinations(range(f), t))
        records = {}
        for roots in combinations(range(7), t):
            root_codes = codes(roots)
            rest = tuple(i for i in range(7) if i not in roots)
            for left in combinations(rest, f-t):
                right = tuple(i for i in rest if i not in left)
                a, b = tuple(sorted(roots+left)), tuple(sorted(roots+right))
                ca = codes(a)*len(marks)+marks.index(tuple(a.index(i) for i in roots))
                cb = codes(b)*len(marks)+marks.index(tuple(b.index(i) for i in roots))
                for root_code in np.unique(root_codes):
                    if selected_roots is not None and int(root_code) not in selected_roots:
                        continue
                    ids = np.flatnonzero(root_codes == root_code)
                    records.setdefault(int(root_code), []).append((ids, ca[ids], cb[ids]))
        norm = comb(7, t)*comb(7-t, f-t)*comb(7-f, f-t)
        for root_code, pieces in sorted(records.items()):
            columns = np.concatenate([v[0] for v in pieces])
            left = np.concatenate([v[1] for v in pieces])
            right = np.concatenate([v[2] for v in pieces])
            keys = np.union1d(left, right)
            a, b = np.searchsorted(keys, left), np.searchsorted(keys, right)
            keep = a <= b
            n = len(keys)
            pairs = [(i, j) for j in range(n) for i in range(j+1)]
            counts = sparse.coo_matrix((np.ones(np.count_nonzero(keep), dtype=np.int64),
                (b[keep]*(b[keep]+1)//2+a[keep], columns[keep])),
                shape=(len(pairs), len(states))).tocsc()
            scale = np.array([1 if i == j else np.sqrt(2) for i, j in pairs])/norm
            blocks.append(dict(t=t, f=f, root_code=root_code, flags=keys.tolist(),
                pairs=pairs, counts=counts, norm=norm,
                operator=(sparse.diags(scale) @ counts).tocsc()))
            print(json.dumps(dict(t=t, f=f, extra_root=root_code, flags=n, entries=counts.nnz)), flush=True)
    return blocks


def compress_factor(factor, tolerance=1e-13):
    if factor.shape[1] == 0:
        return factor
    u, s, _ = np.linalg.svd(factor, full_matrices=False)
    keep = s > tolerance*max(1., float(s[0]))
    return u[:, keep]*s[keep]


def seed_factors(certificate, extras):
    factors = []
    for matrix in certificate_matrices(certificate):
        eig, vec = np.linalg.eigh((matrix+matrix.T)/2)
        keep = eig > 1e-15
        factors.append(vec[:, keep]*np.sqrt(eig[keep]))
    saved = {(b['t'], b['f'], b['root_code']): b for b in certificate.get('extra_blocks', [])}
    for block in extras:
        factor = np.zeros((len(block['flags']), 0))
        key = (block['t'], block['f'], block['root_code'])
        if key in saved:
            b = saved[key]
            old = np.array(b['factor'], dtype=float).reshape(len(b['flags']), -1)/b['denominator']
            factor = np.zeros((len(block['flags']), old.shape[1]))
            ids = {v: i for i, v in enumerate(block['flags'])}
            for i, flag in enumerate(b['flags']):
                if flag not in ids:
                    raise ValueError('Extra certificate flag mismatch')
                factor[ids[flag]] = old[i]
        factors.append(factor)
    return factors


def certify_expanded(patterns, inherited, factors, extras, states, restrictions,
                     state_count, digits=10):
    matrices = [f @ f.T for f in factors[:len(inherited)+1]]
    _, cert, values, common = exact_certificate(patterns, inherited, matrices,
        states, restrictions, state_count, digits=digits, return_values=True)
    denominator = 10**digits
    blocks = []
    for block, factor in zip(extras, factors[len(inherited)+1:]):
        factor = compress_factor(factor)
        integers = np.array([[int(round(v*denominator)) for v in row]
                             for row in factor], dtype=object).reshape(len(block['flags']), -1)
        gram = integers @ integers.T
        norm_den = block['norm']*denominator**2
        from math import lcm
        new_common = lcm(common, norm_den)
        values *= new_common//common
        common = new_common
        # A stored off-diagonal count uses one orientation; its transpose
        # occurs in the ordered configuration list and supplies the factor 2.
        left, right, _ = packed_indices(block)
        coeff = gram[left, right]*np.where(left == right, 1, 2).astype(object)
        counts = block['counts']
        correction = np.empty(len(states), dtype=object)
        for j in range(len(states)):
            correction[j] = sum(int(counts.data[k])*coeff[counts.indices[k]]
                for k in range(counts.indptr[j], counts.indptr[j+1]))
        values += correction*(common//norm_den)
        blocks.append(dict(t=block['t'], f=block['f'], encoding=1, root_code=block['root_code'],
            flags=block['flags'], factor=integers.tolist(), denominator=denominator))
    bound = Q(int(max(values)), common)
    cert.update(format_version=3, extra_blocks=blocks, exact_bound=str(bound),
                worst_pattern=int(np.argmax(values)))
    return bound, cert


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--start-primal', type=Path)
    p.add_argument('--target', type=float, default=.4627479964631095)
    p.add_argument('--rounds', type=int, default=60)
    p.add_argument('--columns', type=int, default=2000, help='Zero uses all cover rows')
    p.add_argument('--add-columns', type=int, default=150)
    p.add_argument('--cuts-per-block', type=int, default=3)
    p.add_argument('--extra-cuts-per-block', type=int, default=8)
    p.add_argument('--seconds', type=float, default=60)
    p.add_argument('--check-every', type=int, default=10)
    p.add_argument('--max-cuts', type=int, default=1200)
    p.add_argument('--keep-recent', type=int, default=700)
    p.add_argument('--digits', type=int, default=10)
    p.add_argument('--resume', action='store_true')
    p.add_argument('--maximize', action='store_true', help='Maximize objective rather than target margin')
    p.add_argument('--lp-solver', choices=['ipm', 'simplex'], default='ipm')
    p.add_argument('--five-roots', type=Path, help='JSON list or diagnostic selecting (5,6) root codes')
    p.add_argument('--all-five-roots', action='store_true')
    args = p.parse_args()
    if min(args.rounds, args.add_columns, args.cuts_per_block, args.extra_cuts_per_block, args.seconds,
           args.check_every, args.keep_recent, args.digits) <= 0 or args.columns < 0:
        p.error('Invalid limits')
    data = json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states, restrictions = archive['states'], archive['restrictions']
        states6 = archive['states6']
    rebuilt, rr, ss, meta = enumerate_seven(data, max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states, rebuilt)
            or not np.array_equal(restrictions, rr) or not np.array_equal(states6, ss)):
        raise ValueError('Cover failed complete regeneration')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    incumbent = json.loads(args.certificate.read_text())
    path = args.output_dir/'certificate.json'
    if path.exists():
        prior = json.loads(path.read_text())
        verify(data, states, restrictions, prior)
        if Q(prior['exact_bound']) < Q(incumbent['exact_bound']):
            incumbent = prior
    verify(data, states, restrictions, incumbent)
    patterns, obj6, inherited = assemble(data)
    if (len(inherited) != len(incumbent['inherited']['blocks']) or
            any(json.loads(json.dumps(b['flags'])) != saved['flags'] for b, saved in
                zip(inherited, incumbent['inherited']['blocks']))):
        raise ValueError('Inherited basis mismatch')
    root = root_block(states, incumbent['root_state_count'])
    five_roots = json.loads(args.five_roots.read_text()) if args.five_roots else None
    if isinstance(five_roots, dict):
        five_roots = five_roots['selected_root_codes']
    extras = extra_blocks(data, states, 'all' if args.all_five_roots else five_roots)
    templates = inherited+[root]+extras
    nin = len(inherited)
    objective = obj6[restrictions].mean(axis=1)
    seeds = seed_factors(incumbent, extras)
    best = Q(incumbent['exact_bound'])
    save(path, incumbent)
    rows, cuts = [], []

    def add_cut(index, factor):
        if factor.shape[1] == 0:
            return
        matrix = factor @ factor.T
        norm = np.linalg.norm(matrix)
        if norm < 1e-25:
            return
        factor = factor/np.sqrt(norm)
        values = block_score(templates[index], matrix/norm)
        if index < nin:
            values = values[restrictions].mean(axis=1)
        rows.append(sparse.csr_matrix(values[None, :]))
        cuts.append((index, factor))

    def moment_matrices(weights):
        return moments(inherited, root, restrictions, weights)+[
            block_moment(b, weights) for b in extras]

    for i, f in enumerate(seeds):
        add_cut(i, f)
    initial_weights = None
    columns = set(np.argsort(objective)[-args.columns:].tolist()) if args.columns else set(range(len(states)))
    columns.update(np.random.default_rng(714).choice(len(states), min(400, len(states)), replace=False).tolist())
    if args.start_primal:
        with np.load(args.start_primal) as saved:
            initial_weights = np.zeros(len(states))
            initial_weights[saved['indices']] = saved['weights']
            columns.update(saved['indices'].tolist())
        for i, matrix in enumerate(moment_matrices(initial_weights)):
            eig, vec = eigh((matrix+matrix.T)/2, subset_by_index=[0, min(7, len(matrix)-1)])
            for j in np.flatnonzero(eig < -1e-10):
                add_cut(i, vec[:, j:j+1])
    empty6 = data['patterns'].index('-'*len(data['tuples']))
    columns.update(np.flatnonzero(np.all(restrictions == empty6, axis=1)).tolist())
    # Include representatives for all new diagonals so a restricted column
    # set does not force an artificial zero common margin.
    for block in extras:
        counts = block['counts'].tocsr()
        for j, (a, b) in enumerate(block['pairs']):
            if a == b:
                row = counts.getrow(j)
                if row.nnz:
                    columns.add(int(row.indices[np.argmax(row.data)]))
    active = np.array(sorted(columns), dtype=np.int64)
    digest = hashlib.sha256(states.tobytes()+restrictions.tobytes()).hexdigest()
    checkpoint = args.output_dir/'checkpoint.npz'
    offset = 0
    history = []
    if args.resume and checkpoint.exists():
        with np.load(checkpoint) as saved:
            if str(saved['digest']) != digest or saved['dimensions'].tolist() != [len(b['flags']) for b in templates]:
                raise ValueError('Checkpoint model mismatch')
            cuts.clear(); rows.clear()
            for j, (i, width) in enumerate(zip(saved['blocks'], saved['widths'])):
                factor = saved['factors'][saved['offsets'][j]:saved['offsets'][j+1]].reshape(len(templates[int(i)]['flags']), int(width))
                add_cut(int(i), factor)
            active, offset = saved['active'], int(saved['round'])
        if (args.output_dir/'report.json').exists():
            history = json.loads((args.output_dir/'report.json').read_text()).get('history', [])
        for i, f in enumerate(seeds):
            add_cut(i, f)

    def make_lp():
        lp = (IncrementalLP(objective[active], args.seconds, args.lp_solver) if args.maximize else
              FeasibilityLP(objective[active], args.seconds, args.target))
        lp.h.setOptionValue('solver', args.lp_solver)
        return lp

    def checkpoint_save(round_number, weights):
        sizes = [f.size for _, f in cuts]
        tmp = args.output_dir/'checkpoint.tmp.npz'
        np.savez_compressed(tmp, blocks=np.array([i for i, _ in cuts]),
            widths=np.array([f.shape[1] for _, f in cuts]), offsets=np.cumsum([0]+sizes),
            factors=np.concatenate([f.ravel() for _, f in cuts]), active=active,
            round=round_number, digest=digest, dimensions=np.array([len(b['flags']) for b in templates]),
            indices=np.flatnonzero(weights), weights=weights[weights != 0])
        tmp.replace(checkpoint)

    lp = make_lp()
    tick = time.monotonic()
    print(json.dumps(dict(baseline=float(best), rows=len(states), dimensions=[len(b['flags']) for b in templates],
                          columns=len(active), cuts=len(cuts), target=args.target)), flush=True)
    for iteration in range(args.rounds):
        selected = [r[:, active] for r in rows]
        traces = [float(np.sum(f*f)) for _, f in cuts]
        result = (lp.solve(selected, np.zeros(len(selected))) if args.maximize else
                  lp.solve(selected, traces, args.target))
        if not result.success:
            print(json.dumps(dict(lp_retry=str(result.message), method='simplex')), flush=True)
            lp.h.setOptionValue('solver', 'simplex')
            lp.h.setOptionValue('presolve', 'on')
            result = (lp.solve(selected, np.zeros(len(selected))) if args.maximize else
                      lp.solve(selected, traces, args.target))
            if not result.success:
                raise RuntimeError(f'LP failed: {result.message}; previous checkpoint retained')
        weights = np.zeros(len(states)); weights[active] = result.x
        matrices = moment_matrices(weights)
        eigensystems = [eigh((m+m.T)/2, subset_by_index=[0,
            min((args.extra_cuts_per_block if i > nin else args.cuts_per_block)-1, len(m)-1)])
            for i, m in enumerate(matrices)]
        alpha = 1. if args.maximize else result.objective_multiplier
        multipliers = np.maximum(0., -result.ineqlin.marginals)
        available = alpha > 1e-12
        scale = alpha if available else 1.
        values = objective.copy() if available else np.zeros(len(states))
        for multiplier, row in zip(multipliers/scale, rows):
            if multiplier > 0:
                values += multiplier*row.toarray().ravel()
        upper = float(np.max(values))
        round_number = offset+iteration+1
        current = dict(round=round_number, cuts=len(cuts), columns=len(active),
            objective=float(objective @ weights), numerical_upper=upper,
            minimum_eigenvalue=min(float(e[0]) for e, _ in eigensystems),
            extra_eigenvalues=[float(e[0]) for e, _ in eigensystems[nin+1:]],
            seconds=time.monotonic()-tick, objective_multiplier=alpha)
        if not args.maximize:
            current['margin'] = result.gamma
        dual_factors = None

        def get_dual_factors():
            grouped = [[] for _ in templates]
            for multiplier, (i, f) in zip(multipliers/scale, cuts):
                if multiplier > 1e-18:
                    grouped[i].append(f*np.sqrt(multiplier))
            return [compress_factor(np.concatenate(fs, axis=1)) if fs else
                    np.zeros((len(b['flags']), 0)) for b, fs in zip(templates, grouped)]

        if available and (upper < float(best)-1e-6 or round_number % args.check_every == 0):
            dual_factors = get_dual_factors()
            bound, cert = certify_expanded(patterns, inherited, dual_factors, extras,
                states, restrictions, incumbent['root_state_count'], args.digits)
            cert.update(coefficient=data['coefficient'], summands=2, tuples=data['tuples'],
                cover6=str(args.cover6), cover7=str(args.cover7),
                search='Convex eigenvector cuts with full (3,5) PSD family')
            if bound < best:
                checked = verify(data, states, restrictions, cert)
                checked.update(complete_cover_reenumerated=True, coverage=meta['meaning']+'; complete cover re-enumerated')
                save(path, cert); save(args.output_dir/'verification.json', checked)
                best, incumbent, seeds = bound, cert, dual_factors
        current.update(certified_upper=str(best), certified_upper_decimal=float(best))
        history.append(current)
        save(args.output_dir/'report.json', dict(history=history, certified_upper=str(best),
            target=args.target, dimensions=[len(b['flags']) for b in templates],
            cover6=str(args.cover6), cover7=str(args.cover7)))
        print(json.dumps(current), flush=True)
        support = np.flatnonzero(weights > 0)
        tmp = args.output_dir/'primal.tmp.npz'
        np.savez_compressed(tmp, indices=support, weights=weights[support]); tmp.replace(args.output_dir/'primal.npz')
        if float(best) < args.target:
            checkpoint_save(round_number, weights)
            break
        missing = np.ones(len(states), dtype=bool); missing[active] = False
        violations = np.flatnonzero(missing & (values > np.max(values[active])+1e-9))
        new = violations[np.argsort(values[violations])[-args.add_columns:]]
        for i, (eig, vec) in enumerate(eigensystems):
            required = 0. if args.maximize else result.gamma
            for j in np.flatnonzero(eig < required-1e-10):
                add_cut(i, vec[:, j:j+1])
        if len(new):
            active = np.union1d(active, new); lp = make_lp()
        if args.max_cuts and len(cuts) > args.max_cuts:
            if dual_factors is None:
                dual_factors = get_dual_factors()
            recent = cuts[-args.keep_recent:]
            cuts.clear(); rows.clear()
            for i, f in enumerate(dual_factors):
                add_cut(i, f)
            for i, f in enumerate(seeds):
                add_cut(i, f)
            for i, f in recent:
                add_cut(i, f)
            lp = make_lp()
        checkpoint_save(round_number, weights)


if __name__ == '__main__':
    main()
