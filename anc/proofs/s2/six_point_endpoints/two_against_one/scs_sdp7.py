"""Warm-started convex seven-point SDP with full-cover certificate checks.

SCS uses lower-triangular column-major svec, unlike Clarabel's upper triangle.
See https://www.cvxgrp.org/scs/api/cones.html and api/python.html.
Numerical primal objectives are not certified lower bounds until exact PSD
verification succeeds. Restricted-row duals are evaluated on the full cover.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from sdp7 import (np,sparse,assemble,restricted_blocks,certificate_matrices,
                  scores,root_scores,exact_certificate,enumerate_seven,save)
from optimal_sdp7 import moments
from verify_sdp7 import verify


def scs_pairing(block):
    n=len(block['flags'])
    pairs=[(i,j) for j in range(n) for i in range(j,n)]
    lookup={pair:k for k,pair in enumerate(block['pairs'])}
    permutation=[lookup[(min(i,j),max(i,j))] for i,j in pairs]
    return pairs,np.array(permutation,dtype=np.int64)


def fit_scs(objective,blocks,matrices,weights,bound,seconds,tolerance,verbose=False,indirect=False):
    import scs
    n=len(objective)
    pairings=[scs_pairing(b) for b in blocks]
    operators=[b['operator'][permutation,:].tocsc() for b,(_,permutation) in zip(blocks,pairings)]
    a=sparse.vstack([sparse.csc_matrix(np.ones((1,n))),-sparse.eye(n,format='csc')]
                    +[-op for op in operators],format='csc')
    rhs=np.zeros(a.shape[0]);rhs[0]=1
    packed=[np.array([q[i,j]*(1 if i==j else np.sqrt(2)) for i,j in pairs])
            for q,(pairs,_) in zip(matrices,pairings)]
    initial_values=objective+sum((op.T @ vector for op,vector in zip(operators,packed)),np.zeros(n))
    bound=max(bound,float(np.max(initial_values))+1e-10)
    dual=np.concatenate([[bound],bound-initial_values]+packed)
    slack=rhs-a @ weights
    solver=scs.SCS(dict(A=a,b=rhs,c=-objective),dict(z=1,l=n,s=[len(b['flags']) for b in blocks]),
                   linear_solver=scs.LinearSolver.CPU_INDIRECT if indirect else scs.LinearSolver.AUTO,
                   verbose=verbose,eps_abs=tolerance,eps_rel=tolerance,max_iters=10000,
                   time_limit_secs=seconds)
    result=solver.solve(warm_start=True,x=weights,y=dual,s=slack)
    output=[];offset=1+n
    for block,(pairs,_) in zip(blocks,pairings):
        q=np.zeros((len(block['flags']),len(block['flags'])))
        for (i,j),value in zip(pairs,result['y'][offset:offset+len(pairs)]):
            q[i,j]=q[j,i]=value/(1 if i==j else np.sqrt(2))
        output.append(q);offset+=len(pairs)
    result['info']['certificate_level']=float(result['y'][0])
    return result['info'],output,np.array(result['x'])


def fit_scs_dual(objective,blocks,matrices,weights,bound,seconds,tolerance,verbose=False,indirect=True):
    """Optimize matrix entries directly; pattern weights are the conic dual."""
    import scs
    pairings=[scs_pairing(b) for b in blocks]
    operators=[b['operator'][permutation,:].tocsc() for b,(_,permutation) in zip(blocks,pairings)]
    operator=sparse.vstack(operators,format='csc')
    n=len(objective);size=operator.shape[0]
    a=sparse.vstack([sparse.hstack([-sparse.csc_matrix(np.ones((n,1))),operator.T]),
                     sparse.hstack([sparse.csc_matrix((size,1)),-sparse.eye(size)])],format='csc')
    rhs=np.r_[-objective,np.zeros(size)]
    c=np.r_[1.,np.zeros(size)]
    packed=np.concatenate([np.array([q[i,j]*(1 if i==j else np.sqrt(2)) for i,j in pairs])
                            for q,(pairs,_) in zip(matrices,pairings)])
    bound=max(bound,float(np.max(objective+operator.T @ packed))+1e-10)
    x=np.r_[bound,packed]
    y=np.r_[weights,operator @ weights]
    solver=scs.SCS(dict(A=a,b=rhs,c=c),dict(l=n,s=[len(b['flags']) for b in blocks]),
                   linear_solver=scs.LinearSolver.CPU_INDIRECT if indirect else scs.LinearSolver.AUTO,
                   verbose=verbose,eps_abs=tolerance,eps_rel=tolerance,max_iters=20000,
                   time_limit_secs=seconds)
    result=solver.solve(warm_start=True,x=x,y=y,s=rhs-a @ x)
    output=[];offset=1
    for block,(pairs,_) in zip(blocks,pairings):
        q=np.zeros((len(block['flags']),len(block['flags'])))
        for (i,j),value in zip(pairs,result['x'][offset:offset+len(pairs)]):
            q[i,j]=q[j,i]=value/(1 if i==j else np.sqrt(2))
        output.append(q);offset+=len(pairs)
    result['info']['certificate_level']=float(result['x'][0])
    return result['info'],output,np.array(result['y'][:n])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6',type=Path,required=True)
    p.add_argument('--cover7',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--primal',type=Path,required=True)
    p.add_argument('--extra-primal',type=Path)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--initial',type=int,default=1200)
    p.add_argument('--add',type=int,default=300)
    p.add_argument('--rounds',type=int,default=4)
    p.add_argument('--seconds',type=float,default=120)
    p.add_argument('--tolerance',type=float,default=1e-8)
    p.add_argument('--verbose',action='store_true')
    p.add_argument('--indirect',action='store_true',help='Use sparse CG instead of an expensive direct factorization')
    p.add_argument('--dual-form',action='store_true',help='Use matrix entries as primal conic variables')
    p.add_argument('--full',action='store_true',help='Use all cover rows')
    args=p.parse_args()
    data=json.loads(args.cover6.read_text())
    with np.load(args.cover7) as a:
        states,restrictions,states6=a['states'],a['restrictions'],a['states6']
    s,r,s6,meta=enumerate_seven(data,max_leaves=len(states)+1)
    if not meta['complete'] or not np.array_equal(s,states) or not np.array_equal(r,restrictions) or not np.array_equal(s6,states6):
        raise ValueError('Cover failed complete re-enumeration')
    certificate=json.loads(args.certificate.read_text())
    verify(data,states,restrictions,certificate)
    existing_path=args.output_dir/'certificate.json'
    if existing_path.exists():
        existing=json.loads(existing_path.read_text())
        verify(data,states,restrictions,existing)
        if Fraction(existing['exact_bound'])<Fraction(certificate['exact_bound']):
            certificate=existing
    patterns,objective6,blocks=assemble(data)
    if len(blocks)!=len(certificate['inherited']['blocks']) or any(
            json.loads(json.dumps(b['flags']))!=saved['flags']
            for b,saved in zip(blocks,certificate['inherited']['blocks'])):
        raise ValueError('Starting certificate flag basis mismatch')
    state_count=certificate['root_state_count']
    matrices=certificate_matrices(certificate)
    best=Fraction(certificate['exact_bound'])
    weights=np.zeros(len(states))
    with np.load(args.primal) as saved:
        weights[saved['indices']]=np.maximum(saved['weights'],0)
    weights/=sum(weights)
    objective=objective6[restrictions].mean(axis=1)
    values=scores(objective6,blocks,matrices[:-1])[restrictions].mean(axis=1)
    values+=root_scores(states,matrices[-1],state_count)
    active=set(np.argsort(values)[-args.initial:].tolist())|set(np.flatnonzero(weights).tolist())
    if args.extra_primal:
        with np.load(args.extra_primal) as saved:
            active.update(int(i) for i in saved['indices'])
    empty6=data['patterns'].index('-'*len(data['tuples']))
    active.update(np.flatnonzero(np.all(restrictions==empty6,axis=1)).tolist())
    if args.full:
        active=set(range(len(states)))
    args.output_dir.mkdir(parents=True,exist_ok=True)
    save(args.output_dir/'certificate.json',certificate)
    initial_check=verify(data,states,restrictions,certificate)
    initial_check.update(complete_cover_reenumerated=True)
    save(args.output_dir/'verification.json',initial_check)
    history=[]
    for iteration in range(args.rounds):
        selected=np.array(sorted(active))
        local=restricted_blocks(blocks,states[selected],restrictions[selected],state_count)
        print(json.dumps(dict(round=iteration+1,active=len(selected),baseline=float(best))),flush=True)
        fitter=fit_scs_dual if args.dual_form else fit_scs
        info,candidate,w=fitter(objective[selected],local,matrices,weights[selected],float(best),
                                 args.seconds,args.tolerance,args.verbose,args.indirect)
        if not np.isfinite(w).all() or not all(np.isfinite(q).all() for q in candidate):
            raise ValueError('SCS returned nonfinite values')
        weights=np.zeros(len(states));weights[selected]=np.maximum(w,0);weights/=sum(weights)
        values=scores(objective6,blocks,candidate[:-1])[restrictions].mean(axis=1)
        values+=root_scores(states,candidate[-1],state_count)
        bound,cert=exact_certificate(patterns,blocks,candidate,states,restrictions,state_count,digits=10)
        cert.update(coefficient=data['coefficient'],summands=2,tuples=data['tuples'],
                    search='Warm-started unrestricted convex SCS solve')
        if bound<best:
            checked=verify(data,states,restrictions,cert)
            checked.update(complete_cover_reenumerated=True)
            save(args.output_dir/'certificate.json',cert);save(args.output_dir/'verification.json',checked)
            best=bound;matrices=certificate_matrices(cert)
        minimum=min(float(np.linalg.eigvalsh(q)[0]) for q in moments(blocks,local[-1],
                    restrictions[selected],weights[selected]))
        # For moment evaluation the root operator above has selected columns;
        # inherited weights are formed from these same selected restrictions.
        row=dict(round=iteration+1,status=info['status'],iterations=info['iter'],
                 primal=float(objective @ weights),active=len(selected),
                 candidate_upper=float(bound),best_upper=float(best),
                 minimum_moment_eigenvalue=minimum,primal_residual=info['res_pri'],
                 dual_residual=info['res_dual'],solve_seconds=info['solve_time']/1000)
        history.append(row);print(json.dumps(row),flush=True)
        np.savez_compressed(args.output_dir/'primal.npz',indices=selected,weights=weights[selected])
        save(args.output_dir/'report.json',dict(best_upper=str(best),history=history))
        violations=np.flatnonzero(values>float(info['certificate_level'])+1e-7)
        fresh=[int(i) for i in violations[np.argsort(values[violations])[::-1]] if int(i) not in active]
        if not fresh:
            break
        active.update(fresh[:args.add])


if __name__=='__main__':
    main()
