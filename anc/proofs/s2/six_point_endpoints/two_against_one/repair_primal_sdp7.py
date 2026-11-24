"""Convex projected-gradient repair of a near-feasible seven-point primal.

Minimizes squared distance of the moment matrices to the shifted PSD cones
over nonnegative weights with total mass one and a target objective. Success
is accepted only after independent exact rational PSD verification.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

from sdp7 import np,sparse,assemble,root_block,restricted_blocks,unpack,save,enumerate_seven
from verify_sdp7 import verify
from verify_primal_sdp7 import verify_primal


def simplex_projection(z):
    ordered=np.sort(z)[::-1]
    cumulative=np.cumsum(ordered)-1
    good=np.flatnonzero(ordered>cumulative/np.arange(1,len(z)+1))
    threshold=cumulative[good[-1]]/(good[-1]+1)
    return np.maximum(z-threshold,0)


def project_weights(z,objective,target):
    """Euclidean projection onto the probability simplex and objective halfspace."""
    p=simplex_projection(z)
    if float(objective @ p)>=target:
        return p
    if target>float(np.max(objective)):
        raise ValueError('Target exceeds every available row objective')
    lo,hi=0.,1.
    while float(objective @ simplex_projection(z+hi*objective))<target:
        hi*=2
    multiplier=(lo+hi)/2
    for _ in range(60):
        p=simplex_projection(z+multiplier*objective)
        value=float(objective @ p)
        if abs(value-target)<2e-14:
            return p
        if value<target:
            lo=multiplier
        else:
            hi=multiplier
        selected=objective[p>0]
        slope=float(np.sum((selected-selected.mean())**2)) if len(selected) else 0.
        new=multiplier+(target-value)/slope if slope>1e-30 else (lo+hi)/2
        multiplier=new if lo<new<hi else (lo+hi)/2
    return simplex_projection(z+hi*objective)


class RepairObjective:
    def __init__(self,blocks,margin):
        self.blocks=blocks
        self.margin=margin

    def __call__(self,w):
        value=0.
        gradient=np.zeros(len(w))
        minimum=float('inf')
        for b in self.blocks:
            matrix=unpack(b['operator'] @ w,b['pairs'],len(b['flags']))
            eigenvalues,vectors=np.linalg.eigh((matrix+matrix.T)/2)
            minimum=min(minimum,float(eigenvalues[0]))
            negative=np.minimum(eigenvalues-self.margin,0)
            value+=.5*float(negative @ negative)
            if np.any(negative):
                correction=(vectors*negative) @ vectors.T
                packed=np.array([correction[i,j]*(1 if i==j else np.sqrt(2)) for i,j in b['pairs']])
                gradient+=b['operator'].T @ packed
        return value,gradient,minimum


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6',type=Path,required=True)
    p.add_argument('--cover7',type=Path,required=True)
    p.add_argument('--upper-certificate',type=Path,required=True)
    p.add_argument('--primal',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--tolerance',type=float,default=1e-5)
    p.add_argument('--margin',type=float,default=1e-11)
    p.add_argument('--iterations',type=int,default=10000)
    p.add_argument('--gap-fraction',type=float,default=.95,
                   help='Seek a lower point this fraction of the allowed gap below the upper')
    p.add_argument('--extra-primal',type=Path,
                   help='Allow additional row indices from another primal, initially with zero weight')
    args=p.parse_args()
    data=json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states,restrictions,states6=archive['states'],archive['restrictions'],archive['states6']
    rebuilt,rr,ss,meta=enumerate_seven(data,max_leaves=len(states)+1)
    if not meta['complete'] or not np.array_equal(states,rebuilt) or not np.array_equal(rr,restrictions) or not np.array_equal(ss,states6):
        raise ValueError('Archive failed complete re-enumeration')
    upper=json.loads(args.upper_certificate.read_text())
    verify(data,states,restrictions,upper)
    _,objective6,blocks=assemble(data)
    def check_basis(certificate):
        if (len(blocks)!=len(certificate['inherited']['blocks']) or
                any(json.loads(json.dumps(b['flags']))!=saved['flags']
                    for b,saved in zip(blocks,certificate['inherited']['blocks']))):
            raise ValueError('Upper certificate uses a different SDP flag basis')
    check_basis(upper)
    with np.load(args.primal) as saved:
        indices=saved['indices']
        w=np.maximum(saved['weights'],0)
    if args.extra_primal:
        with np.load(args.extra_primal) as saved:
            combined=np.union1d(indices,saved['indices'])
        expanded=np.zeros(len(combined))
        expanded[np.searchsorted(combined,indices)]=w
        indices,w=combined,expanded
    w/=sum(w)
    objective=objective6[restrictions[indices]].mean(axis=1)
    if not 0<args.gap_fraction<1:
        p.error('Require 0<gap-fraction<1')
    target=float(Fraction(upper['exact_bound']))-args.gap_fraction*args.tolerance
    w=project_weights(w,objective,target)
    local=restricted_blocks(blocks,states[indices],restrictions[indices],upper['root_state_count'])
    function=RepairObjective(local,args.margin)
    # A power estimate initializes a backtracking Lipschitz bound.
    rng=np.random.default_rng(774)
    direction=rng.normal(size=len(w));direction/=np.linalg.norm(direction)
    for _ in range(30):
        transformed=sum((b['operator'].T @ (b['operator'] @ direction) for b in local),np.zeros(len(w)))
        lipschitz=float(np.linalg.norm(transformed))
        direction=transformed/max(lipschitz,1e-30)
    lipschitz=max(lipschitz,1e-10)
    y=w.copy();acceleration=1.
    args.output_dir.mkdir(parents=True,exist_ok=True)
    tick=time.monotonic();history=[]
    print(json.dumps(dict(columns=len(w),target=target,upper=float(Fraction(upper['exact_bound'])),
                         initial=function(w)[0],lipschitz=lipschitz)),flush=True)
    for iteration in range(args.iterations):
        # The global operator norm is overly conservative near a PSD face.
        # Try a larger step and retain it only when the quadratic upper model
        # passes an actual objective check.
        lipschitz=max(lipschitz*.8,1e-12)
        value,gradient,_=function(y)
        while True:
            candidate=project_weights(y-gradient/lipschitz,objective,target)
            next_value,_,minimum=function(candidate)
            delta=candidate-y
            if next_value<=value+float(gradient @ delta)+.5*lipschitz*float(delta @ delta)+1e-10*max(value,next_value)+1e-28:
                break
            lipschitz*=2
        next_acceleration=(1+np.sqrt(1+4*acceleration**2))/2
        if float((y-candidate) @ (candidate-w))>0:
            next_acceleration=1.
        y=candidate+((acceleration-1)/next_acceleration)*(candidate-w)
        w=candidate;acceleration=next_acceleration
        if (iteration+1)%250==0 or minimum>0:
            refreshed=json.loads(args.upper_certificate.read_text())
            if Fraction(refreshed['exact_bound'])<Fraction(upper['exact_bound']):
                verify(data,states,restrictions,refreshed)
                check_basis(refreshed)
                upper=refreshed
                target=float(Fraction(upper['exact_bound']))-args.gap_fraction*args.tolerance
            row=dict(iteration=iteration+1,objective=float(objective @ w),
                     psd_distance_squared=2*next_value,minimum_eigenvalue=minimum,
                     seconds=time.monotonic()-tick)
            if minimum>0:
                integers=[max(0,int(round(float(v)*10**20))) for v in w]
                try:
                    checked=verify_primal(data,states,restrictions,upper,indices.tolist(),integers)
                    temporary=args.output_dir/'primal.tmp.npz'
                    np.savez_compressed(temporary,indices=indices,weights=w)
                    temporary.replace(args.output_dir/'primal.npz')
                    save(args.output_dir/'primal_certificate.json',dict(coefficient=data['coefficient'],
                         indices=indices.tolist(),weight_numerators=integers))
                    save(args.output_dir/'optimality_verification.json',checked)
                    row.update(certified_gap=checked['gap'],exact_primal_psd=True)
                    history.append(row)
                    save(args.output_dir/'report.json',dict(status='Exact primal verified',history=history))
                    print(json.dumps(row),flush=True)
                    if checked['gap']<=args.tolerance:
                        break
                except ValueError as exc:
                    row['exact_check_failure']=str(exc)
            history.append(row)
            print(json.dumps(row),flush=True)
            temporary=args.output_dir/'primal.tmp.npz'
            np.savez_compressed(temporary,indices=indices,weights=w)
            temporary.replace(args.output_dir/'primal.npz')
            save(args.output_dir/'report.json',dict(status='Repair in progress',history=history))


if __name__=='__main__':
    main()
