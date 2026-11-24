"""Search full-square PSD factors for an exact six-point upper certificate.

The numerical search is nonconvex; every saved bound is independently
checked on the full exact cover. No optimality claim is made.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import time

from sdp6 import np, assemble, scores, certify, verify
from sdp7 import save
from flag_sdp import unpack
from scipy.optimize import minimize


class FactorObjective:
    def __init__(self, objective, blocks, temperature):
        self.objective, self.blocks, self.temperature = objective, blocks, temperature
        self.dimensions = [len(b['flags']) for b in blocks]
        self.offsets = np.cumsum([0]+[n*n for n in self.dimensions])

    def factors(self, x):
        return [x[self.offsets[i]:self.offsets[i+1]].reshape(n, n)
                for i, n in enumerate(self.dimensions)]

    def __call__(self, x):
        factors = self.factors(x)
        values = scores(self.objective, self.blocks, [f @ f.T for f in factors])
        self.maximum = float(np.max(values))
        weights = np.exp((values-self.maximum)/self.temperature)
        total = weights.sum()
        weights /= total
        gradients = [(2*unpack(b['operator'] @ weights, b['pairs'], len(b['flags'])) @ f).ravel()
                     for b, f in zip(self.blocks, factors)]
        return self.maximum+self.temperature*np.log(total), np.concatenate(gradients)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--temperatures', type=float, nargs='+', default=[1e-3, 1e-4, 1e-5, 1e-6])
    p.add_argument('--iterations', type=int, default=700)
    p.add_argument('--digits', type=int, default=10)
    p.add_argument('--stop-below', type=Q)
    args = p.parse_args()
    if min(args.temperatures) <= 0 or args.iterations < 1 or args.digits < 1:
        p.error('Require positive numerical limits')
    data = json.loads(args.cover.read_text())
    cert = json.loads(args.certificate.read_text())
    existing_path = args.output_dir/'certificate.json'
    if existing_path.exists():
        existing = json.loads(existing_path.read_text())
        if Q(existing['exact_bound']) < Q(cert['exact_bound']):
            cert = existing
    checked = verify(data, cert)
    patterns, objective, blocks = assemble(data)
    if len(blocks) != len(cert['blocks']) or any(
            json.loads(json.dumps(b['flags'])) != old['flags'] for b, old in zip(blocks, cert['blocks'])):
        raise ValueError('Flag basis mismatch')
    factors = []
    for old in cert['blocks']:
        factor = np.array([[float(Q(v)) for v in row] for row in old['L']])
        eigenvalues, vectors = np.linalg.eigh(factor @ factor.T)
        factors.append(vectors*np.sqrt(np.maximum(eigenvalues, 1e-8)))
    x = np.concatenate([f.ravel() for f in factors])
    best = Q(cert['exact_bound'])
    args.output_dir.mkdir(parents=True, exist_ok=True)
    save(args.output_dir/'certificate.json', cert)
    save(args.output_dir/'verification.json', checked)
    history = []
    print(json.dumps(dict(baseline=float(best), variables=len(x), patterns=len(patterns))), flush=True)
    for temperature in args.temperatures:
        function = FactorObjective(objective, blocks, temperature)
        tick = last = time.monotonic()
        def callback(current):
            nonlocal last
            if time.monotonic()-last > 25:
                print(json.dumps(dict(temperature=temperature, numerical_max=function.maximum,
                                      seconds=time.monotonic()-tick)), flush=True)
                last = time.monotonic()
        result = minimize(function, x, jac=True, method='L-BFGS-B', callback=callback,
                          options=dict(maxiter=args.iterations, maxls=40, maxcor=15, ftol=1e-14, gtol=1e-8))
        x = result.x
        bound, candidate = certify(patterns.tolist(), blocks,
                                  [f @ f.T for f in function.factors(x)], args.digits)
        candidate.update(summands=2, coefficient=data['coefficient'], tuples=data['tuples'],
                         exact_bound=str(bound), search='Full-square PSD factor refinement; all six-point rows')
        row = dict(temperature=temperature, iterations=int(result.nit), exact_bound=str(bound),
                   decimal_bound=float(bound), status=str(result.message), seconds=time.monotonic()-tick)
        history.append(row)
        if bound < best:
            checked = verify(data, candidate)
            save(args.output_dir/'certificate.json', candidate)
            save(args.output_dir/'verification.json', checked)
            best = bound
        save(args.output_dir/'report.json', dict(method=__doc__, cover=str(args.cover),
             seed=str(args.certificate), exact_bound=str(best), decimal_bound=float(best), history=history))
        print(json.dumps(row), flush=True)
        if args.stop_below is not None and best < args.stop_below:
            break


if __name__ == '__main__':
    main()
