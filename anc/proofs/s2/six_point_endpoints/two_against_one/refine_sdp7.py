"""Refine every seven-point PSD matrix through unrestricted square factors.

This is a nonconvex numerical search for rigorous certificates, not a proof
of convergence to the unrestricted convex SDP optimum. Every matrix is L L^T
with a full square L; inherited matrices are not restricted to seed rays.
The smooth maximum uses ALL seven-point rows. An independent exact verifier
checks any improved bound before it is saved.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

from sdp7 import (np, assemble, root_block, unpack, scores, root_scores,
                  enumerate_seven, certificate_matrices, exact_certificate, save)
from verify_sdp7 import verify
from scipy.optimize import minimize


class FactorObjective:
    def __init__(self, objective6, blocks6, root, restrictions, temperature):
        self.objective6, self.blocks6, self.root = objective6, blocks6, root
        self.restrictions, self.temperature = restrictions, temperature
        self.blocks = blocks6+[root]
        self.dimensions = [len(b['flags']) for b in self.blocks]
        self.offsets = np.cumsum([0]+[n*n for n in self.dimensions])
        self.evaluations = 0

    def factors(self, x):
        return [x[self.offsets[i]:self.offsets[i+1]].reshape(n,n)
                for i,n in enumerate(self.dimensions)]

    def __call__(self, x):
        factors = self.factors(x)
        matrices = [factor @ factor.T for factor in factors]
        value6 = scores(self.objective6, self.blocks6, matrices[:-1])
        root_coeff = np.array([matrices[-1][i,j]*(1 if i==j else np.sqrt(2))
                               for i,j in self.root['pairs']])
        values = value6[self.restrictions].mean(axis=1)+self.root['operator'].T @ root_coeff
        maximum = float(np.max(values))
        exponents = np.exp((values-maximum)/self.temperature)
        weights = exponents/exponents.sum()
        objective = maximum+self.temperature*np.log(exponents.sum())
        weights6 = np.bincount(self.restrictions.ravel(),
                               weights=np.repeat(weights/7,7), minlength=len(value6))
        gradients = []
        for block,factor in zip(self.blocks6,factors[:-1]):
            moment = unpack(block['operator'] @ weights6,block['pairs'],len(block['flags']))
            gradients.append((2*moment @ factor).ravel())
        moment = unpack(self.root['operator'] @ weights,self.root['pairs'],self.dimensions[-1])
        gradients.append((2*moment @ factors[-1]).ravel())
        self.evaluations += 1
        self.last_maximum = maximum
        return objective,np.concatenate(gradients)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6',type=Path,required=True)
    p.add_argument('--cover7',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--temperatures',type=float,nargs='+',default=[1e-4,1e-5,1e-6,1e-7])
    p.add_argument('--iterations',type=int,default=300)
    p.add_argument('--digits',type=int,default=10)
    p.add_argument('--stop-below',type=Fraction,help='Stop after an exact upper is strictly below this value')
    p.add_argument('--initial-eigenvalue-floor',type=float,default=1e-10,
                   help='Initial Gram eigenvalue floor; larger values explore new PSD directions')
    args=p.parse_args()
    if min(args.temperatures)<=0 or args.iterations<=0 or args.digits<=0 or args.initial_eigenvalue_floor<0:
        p.error('Temperatures, iterations and digits must be positive')
    data=json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states,restrictions=archive['states'],archive['restrictions']
        states6=archive['states6']
    rebuilt,restrictions2,states62,meta=enumerate_seven(data,max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states,rebuilt)
            or not np.array_equal(restrictions,restrictions2) or not np.array_equal(states6,states62)):
        raise ValueError('Cover failed complete re-enumeration')
    certificate=json.loads(args.certificate.read_text())
    if certificate.get('format_version') != 2:
        raise ValueError('Use refine_expanded_sdp7.py for certificates with extra PSD blocks')
    verify(data,states,restrictions,certificate)
    existing_path=args.output_dir/'certificate.json'
    prior_history=[]
    if existing_path.exists():
        existing=json.loads(existing_path.read_text())
        verify(data,states,restrictions,existing)
        if Fraction(existing['exact_bound'])<Fraction(certificate['exact_bound']):
            certificate=existing
        report_path=args.output_dir/'report.json'
        if report_path.exists():
            prior_history=json.loads(report_path.read_text()).get('history',[])
    patterns,objective,blocks=assemble(data)
    for block,saved in zip(blocks,certificate['inherited']['blocks']):
        if json.loads(json.dumps(block['flags']))!=saved['flags']:
            raise ValueError('Starting certificate flag basis mismatch')
    if len(blocks)!=len(certificate['inherited']['blocks']):
        raise ValueError('Starting certificate block count mismatch')
    state_count=certificate['root_state_count']
    root=root_block(states,state_count)
    matrices=certificate_matrices(certificate)
    # Full square factors cover the entire PSD cone, including new directions
    # absent from low-rank seed factors. A tiny positive eigenvalue floor keeps
    # those directions available to first-order optimization.
    factors=[]
    for matrix in matrices:
        eigenvalues,vectors=np.linalg.eigh((matrix+matrix.T)/2)
        factors.append(vectors*np.sqrt(np.maximum(eigenvalues,args.initial_eigenvalue_floor)))
    x=np.concatenate([factor.ravel() for factor in factors])
    best=Fraction(certificate['exact_bound'])
    args.output_dir.mkdir(parents=True,exist_ok=True)

    def accept(cert):
        checked=verify(data,states,restrictions,cert)
        checked.update(complete_cover_reenumerated=True,
                       coverage=meta['meaning']+'; complete cover re-enumerated')
        save(args.output_dir/'certificate.json',cert)
        save(args.output_dir/'verification.json',checked)

    accept(certificate)
    history=prior_history
    print(json.dumps(dict(baseline=float(best),variables=len(x),patterns=len(states))),flush=True)
    for temperature in args.temperatures:
        objective_function=FactorObjective(objective,blocks,root,restrictions,temperature)
        tick=time.monotonic()
        last_report=tick

        def callback(current):
            nonlocal last_report
            now=time.monotonic()
            if now-last_report>25:
                print(json.dumps(dict(temperature=temperature,
                     evaluations=objective_function.evaluations,
                     numerical_max=objective_function.last_maximum,
                     seconds=now-tick)),flush=True)
                last_report=now

        result=minimize(objective_function,x,jac=True,method='L-BFGS-B',callback=callback,
                        options=dict(maxiter=args.iterations,maxls=40,maxcor=15,
                                     ftol=1e-14,gtol=1e-8))
        x=result.x
        objective_function(x)
        factors=objective_function.factors(x)
        matrices=[factor @ factor.T for factor in factors]
        bound,cert=exact_certificate(patterns,blocks,matrices,states,restrictions,state_count,
                                     digits=args.digits)
        cert.update(coefficient=data['coefficient'],summands=2,tuples=data['tuples'],
                    cover6=str(args.cover6),cover7=str(args.cover7),
                    search='Unrestricted full square PSD factors; full-cover smooth maximum')
        row=dict(temperature=temperature,iterations=int(result.nit),
                 evaluations=objective_function.evaluations,status=str(result.message),
                 seconds=time.monotonic()-tick,numerical_max=objective_function.last_maximum,
                 exact_bound=str(bound),exact_bound_decimal=float(bound))
        history.append(row)
        print(json.dumps(row),flush=True)
        if bound<best:
            accept(cert)
            best=bound
        save(args.output_dir/'report.json',dict(method='Full PSD factor refinement (nonconvex)',
             unrestricted_matrix_entries=True,all_cover_rows=True,patterns=len(states),
             iterations_per_temperature=args.iterations,temperatures=args.temperatures,
             cover6=str(args.cover6),cover7=str(args.cover7),seed_certificate=str(args.certificate),
             exact_bound=str(best),exact_bound_decimal=float(best),history=history))
        if args.stop_below is not None and best < args.stop_below:
            break


if __name__=='__main__':
    main()
