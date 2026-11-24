"""Search for expanded seven-point upper certificates using Gram factors.

Inherited matrices have full square factors. New (3,5) matrices use a
configurable factor width. This numerical search is nonconvex and does
not prove SDP optimality. Exact full-cover checks validate saved bounds.
"""
import argparse
import hashlib
from fractions import Fraction as Q
import json
from pathlib import Path
import time

from expanded_sdp7 import (np, assemble, extra_blocks, seed_factors,
    certify_expanded, save, enumerate_seven, unpack, verify, block_score, block_moment)
from sdp7 import root_block
from refine_sdp7 import FactorObjective
from scipy.optimize import minimize


class ExpandedObjective:
    def __init__(self, objective6, inherited, root, extras, restrictions, temperature, widths):
        self.base = FactorObjective(objective6, inherited, root, restrictions, temperature)
        self.extras, self.widths = extras, widths
        self.shapes = [(n, n) for n in self.base.dimensions]+[
            (len(b['flags']), width) for b, width in zip(extras, widths)]
        self.offsets = np.cumsum([0]+[a*b for a, b in self.shapes])
        self.evaluations = 0

    def factors(self, x):
        return [x[self.offsets[i]:self.offsets[i+1]].reshape(shape)
                for i, shape in enumerate(self.shapes)]

    def __call__(self, x):
        factors = self.factors(x)
        matrices = [f @ f.T for f in factors]
        from sdp7 import scores
        nbase = len(self.base.blocks)
        value6 = scores(self.base.objective6, self.base.blocks6, matrices[:nbase-1])
        values = value6[self.base.restrictions].mean(axis=1)
        for block, matrix in zip([self.base.root]+self.extras, matrices[nbase-1:]):
            values += block_score(block, matrix)
        maximum = float(np.max(values))
        exponents = np.exp((values-maximum)/self.base.temperature)
        weights = exponents/exponents.sum()
        weights6 = np.bincount(self.base.restrictions.ravel(),
            weights=np.repeat(weights/7, 7), minlength=len(value6))
        gradients = []
        for block, factor in zip(self.base.blocks6, factors[:nbase-1]):
            moment = unpack(block['operator'] @ weights6, block['pairs'], len(block['flags']))
            gradients.append((2*moment @ factor).ravel())
        for block, factor in zip([self.base.root]+self.extras, factors[nbase-1:]):
            moment = block_moment(block, weights)
            gradients.append((2*moment @ factor).ravel())
        self.evaluations += 1
        self.last_maximum = maximum
        return maximum+self.base.temperature*np.log(exponents.sum()), np.concatenate(gradients)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--extra-rank', type=int, default=24)
    p.add_argument('--five-rank', type=int, help='Separate width for optional (5,6) factors')
    p.add_argument('--iterations', type=int, default=1500)
    p.add_argument('--temperatures', type=float, nargs='+', default=[1e-4, 1e-5, 1e-6])
    p.add_argument('--digits', type=int, default=10)
    p.add_argument('--initial-floor', type=float, default=1e-5)
    p.add_argument('--resume', action='store_true', help='Restore the latest numerical factor checkpoint')
    p.add_argument('--target', type=float, default=.4627479964631095)
    p.add_argument('--five-roots', type=Path)
    p.add_argument('--all-five-roots', action='store_true')
    args = p.parse_args()
    if min(args.extra_rank, args.iterations, args.digits, *args.temperatures) <= 0 or args.initial_floor < 0:
        p.error('Invalid numerical limits')
    data = json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states, restrictions, states6 = archive['states'], archive['restrictions'], archive['states6']
    rebuilt, rr, ss, meta = enumerate_seven(data, max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states, rebuilt)
            or not np.array_equal(restrictions, rr) or not np.array_equal(states6, ss)):
        raise ValueError('Cover failed complete regeneration')
    incumbent = json.loads(args.certificate.read_text())
    history = []
    if (args.output_dir/'certificate.json').exists():
        previous = json.loads((args.output_dir/'certificate.json').read_text())
        verify(data, states, restrictions, previous)
        if Q(previous['exact_bound']) < Q(incumbent['exact_bound']):
            incumbent = previous
        if (args.output_dir/'report.json').exists():
            history = json.loads((args.output_dir/'report.json').read_text()).get('history', [])
    verify(data, states, restrictions, incumbent)
    patterns, objective6, inherited = assemble(data)
    if (len(inherited) != len(incumbent['inherited']['blocks']) or any(
            json.loads(json.dumps(b['flags'])) != saved['flags'] for b, saved in
            zip(inherited, incumbent['inherited']['blocks']))):
        raise ValueError('Inherited flag mismatch')
    root = root_block(states, incumbent['root_state_count'])
    five_roots = json.loads(args.five_roots.read_text()) if args.five_roots else None
    if isinstance(five_roots, dict):
        five_roots = five_roots['selected_root_codes']
    extras = extra_blocks(data, states, 'all' if args.all_five_roots else five_roots)
    seeds = seed_factors(incumbent, extras)
    factors = []
    for seed in seeds[:len(inherited)+1]:
        matrix = seed @ seed.T
        eigenvalues, vectors = np.linalg.eigh(matrix)
        factors.append(vectors*np.sqrt(np.maximum(eigenvalues, args.initial_floor)))
    rng = np.random.default_rng(734)
    widths = [min(len(b['flags']), args.five_rank if b['t'] == 5 and args.five_rank is not None
                  else args.extra_rank) for b in extras]
    for block, seed, width in zip(extras, seeds[len(inherited)+1:], widths):
        factor = rng.normal(size=(len(block['flags']), width))*np.sqrt(args.initial_floor/width)
        if seed.shape[1]:
            u, s, _ = np.linalg.svd(seed, full_matrices=False)
            k = min(width, len(s))
            factor[:, :k] += u[:, :k]*s[:k]
        factors.append(factor)
    x = np.concatenate([f.ravel() for f in factors])
    checkpoint = args.output_dir/'factor_checkpoint.npz'
    digest = hashlib.sha256(states.tobytes()+restrictions.tobytes()+
        json.dumps(data['coefficient']).encode()+
        json.dumps([(b['t'], b['f'], b['root_code'], b['flags']) for b in extras]).encode()).hexdigest()
    if args.resume and checkpoint.exists():
        with np.load(checkpoint) as saved:
            if str(saved['digest']) != digest or saved['widths'].tolist() != widths or saved['x'].shape != x.shape:
                raise ValueError('Numerical factor checkpoint mismatch')
            x = saved['x']

    def save_factors(current, temperature):
        tmp = args.output_dir/'factor_checkpoint.tmp.npz'
        np.savez_compressed(tmp, x=current, widths=widths, digest=digest, temperature=temperature)
        tmp.replace(checkpoint)
    best = Q(incumbent['exact_bound'])
    save(args.output_dir/'certificate.json', incumbent)
    print(json.dumps(dict(baseline=float(best), variables=len(x), extra_widths=widths)), flush=True)
    for temperature in args.temperatures:
        function = ExpandedObjective(objective6, inherited, root, extras, restrictions, temperature, widths)
        tick = last = time.monotonic()

        def callback(current):
            nonlocal last
            now = time.monotonic()
            if now-last > 25:
                save_factors(current, temperature)
                print(json.dumps(dict(temperature=temperature, evaluations=function.evaluations,
                    numerical_max=function.last_maximum, seconds=now-tick)), flush=True)
                last = now

        result = minimize(function, x, jac=True, method='L-BFGS-B', callback=callback,
            options=dict(maxiter=args.iterations, maxls=30, maxcor=15, ftol=1e-14, gtol=1e-8))
        x = result.x
        save_factors(x, temperature)
        function(x)
        factors = function.factors(x)
        bound, cert = certify_expanded(patterns, inherited, factors, extras,
            states, restrictions, incumbent['root_state_count'], args.digits)
        cert.update(coefficient=data['coefficient'], summands=2, tuples=data['tuples'],
            cover6=str(args.cover6), cover7=str(args.cover7),
            search=dict(method='Full-cover Gram-factor refinement', extra_rank=args.extra_rank))
        if bound < best:
            checked = verify(data, states, restrictions, cert)
            checked.update(complete_cover_reenumerated=True, coverage=meta['meaning']+'; complete cover re-enumerated')
            save(args.output_dir/'certificate.json', cert); save(args.output_dir/'verification.json', checked)
            best = bound
        row = dict(temperature=temperature, iterations=int(result.nit), evaluations=function.evaluations,
            seconds=time.monotonic()-tick, numerical_max=function.last_maximum,
            exact_bound=str(bound), exact_bound_decimal=float(bound), status=str(result.message))
        history.append(row)
        save(args.output_dir/'report.json', dict(history=history, certified_upper=str(best),
            extra_rank=args.extra_rank, cover6=str(args.cover6), cover7=str(args.cover7)))
        print(json.dumps(row), flush=True)
        if best < Q(str(args.target)):
            break


if __name__ == '__main__':
    main()
