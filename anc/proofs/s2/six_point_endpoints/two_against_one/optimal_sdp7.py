"""Convex eigenvector-cut outer approximation of the seven-point primal SDP.

All cover rows are LP variables. Each PSD condition is separated by its
negative eigenvectors. LP dual multipliers combine PSD cut matrices into a
universal upper certificate. A primal objective is a lower bound on the SDP
optimum only after the original (unshifted) moment matrices are proved PSD.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import hashlib

from sdp7 import (np, sparse, assemble, root_block, unpack, scores, root_scores,
                  enumerate_seven, certificate_matrices, exact_certificate, save)
from verify_sdp7 import verify
from scipy.optimize import linprog
from types import SimpleNamespace


class IncrementalLP:
    """Reuse a HiGHS dual-simplex basis when new PSD cuts are appended."""
    def __init__(self, objective, seconds, solver='simplex'):
        import highspy
        self.highspy=highspy
        self.seconds=seconds
        h=self.h=highspy.Highs()
        for name,value in [('output_flag',False),('solver',solver),('simplex_strategy',1),
                           ('presolve','off'),('primal_feasibility_tolerance',1e-10),
                           ('dual_feasibility_tolerance',1e-9),('time_limit',seconds)]:
            h.setOptionValue(name,value)
        if solver=='ipm':
            h.setOptionValue('run_crossover','off')
            h.setOptionValue('ipm_optimality_tolerance',1e-11)
        n=len(objective)
        h.addCols(n,-objective,np.zeros(n),np.full(n,highspy.kHighsInf),0,
                  np.zeros(n+1,dtype=np.int32),np.array([],dtype=np.int32),np.array([],dtype=float))
        h.addRows(1,np.array([1.]),np.array([1.]),n,np.array([0,n],dtype=np.int32),
                  np.arange(n,dtype=np.int32),np.ones(n))
        self.added=0

    def solve(self,rows,rhs):
        if self.added<len(rows):
            matrix=sparse.vstack(rows[self.added:],format='csr')
            count=matrix.shape[0]
            self.h.addRows(count,np.full(count,-self.highspy.kHighsInf),rhs[self.added:],
                           matrix.nnz,matrix.indptr.astype(np.int32),
                           matrix.indices.astype(np.int32),-matrix.data)
            self.added=len(rows)
        self.h.setOptionValue('time_limit',self.h.getRunTime()+self.seconds)
        self.h.run()
        status=self.h.getModelStatus()
        solution=self.h.getSolution()
        info=self.h.getInfo()
        return SimpleNamespace(success=status==self.highspy.HighsModelStatus.kOptimal,
              message=str(status),x=np.array(solution.col_value),
              ineqlin=SimpleNamespace(marginals=np.array(solution.row_dual[1:])),
              fun=info.objective_function_value)


class FeasibilityLP:
    """Maximize a common moment margin at a specified primal objective."""
    def __init__(self,objective,seconds,target):
        import highspy
        self.highspy=highspy
        self.seconds=seconds
        h=self.h=highspy.Highs()
        for name,value in [('output_flag',False),('solver','ipm'),('run_crossover','off'),
                           ('ipm_optimality_tolerance',1e-11),
                           ('presolve','off'),('primal_feasibility_tolerance',1e-10),
                           ('dual_feasibility_tolerance',1e-9),('time_limit',seconds)]:
            h.setOptionValue(name,value)
        n=len(objective)
        lower=np.r_[np.zeros(n),-highspy.kHighsInf]
        costs=np.r_[np.zeros(n),-1.]
        h.addCols(n+1,costs,lower,np.full(n+1,highspy.kHighsInf),0,
                  np.zeros(n+2,dtype=np.int32),np.array([],dtype=np.int32),np.array([],dtype=float))
        rows=sparse.csr_matrix(np.vstack([np.r_[np.ones(n),0],np.r_[objective,0]]))
        h.addRows(2,np.array([1.,target]),np.array([1.,highspy.kHighsInf]),rows.nnz,
                  rows.indptr.astype(np.int32),rows.indices.astype(np.int32),rows.data)
        self.added=0

    def solve(self,rows,traces,target):
        self.h.changeRowBounds(1,target,self.highspy.kHighsInf)
        if self.added<len(rows):
            matrix=sparse.hstack([-sparse.vstack(rows[self.added:],format='csr'),
                                  sparse.csr_matrix(np.array(traces[self.added:])[:,None])],format='csr')
            count=matrix.shape[0]
            self.h.addRows(count,np.full(count,-self.highspy.kHighsInf),np.zeros(count),matrix.nnz,
                           matrix.indptr.astype(np.int32),matrix.indices.astype(np.int32),matrix.data)
            self.added=len(rows)
        self.h.setOptionValue('time_limit',self.h.getRunTime()+self.seconds)
        self.h.run()
        status=self.h.getModelStatus()
        solution=self.h.getSolution()
        return SimpleNamespace(success=status==self.highspy.HighsModelStatus.kOptimal,
              message=str(status),x=np.array(solution.col_value[:-1]),
              gamma=float(solution.col_value[-1]),objective_multiplier=float(solution.row_dual[1]),
              ineqlin=SimpleNamespace(marginals=np.array(solution.row_dual[2:])))


def block_score(block, matrix):
    coefficients=np.array([matrix[i,j]*(1 if i==j else np.sqrt(2)) for i,j in block['pairs']])
    return np.asarray(block['operator'].T @ coefficients).ravel()


def moments(blocks,root,restrictions,weights):
    weights6=np.bincount(restrictions.ravel(),weights=np.repeat(weights/7,7),
                         minlength=blocks[0]['operator'].shape[1])
    return [unpack(b['operator'] @ weights6,b['pairs'],len(b['flags'])) for b in blocks]+[
        unpack(root['operator'] @ weights,root['pairs'],len(root['flags']))]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6',type=Path,required=True)
    p.add_argument('--cover7',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=80)
    p.add_argument('--tolerance',type=float,default=1e-5)
    p.add_argument('--eigen-tolerance',type=float,default=1e-9)
    p.add_argument('--margin',type=float,default=1e-10,
                   help='Small positive margin sought in primal PSD moments')
    p.add_argument('--cuts-per-block',type=int,default=2)
    p.add_argument('--lp-seconds',type=float,default=90)
    p.add_argument('--method',choices=['highs-ds','highs-ipm'],default='highs-ds')
    p.add_argument('--incremental',action='store_true',help='Use highspy with LP basis reuse')
    p.add_argument('--check-every',type=int,default=5,
                   help='Independently check upper certificates at this round interval')
    p.add_argument('--feasibility',action='store_true',
                   help='Seek a PSD primal at upper minus 0.8*tolerance, maximizing common margin')
    p.add_argument('--columns',type=int,default=0,
                   help='Start with this many tight cover rows and price in missing variables; zero uses all')
    p.add_argument('--add-columns',type=int,default=100)
    p.add_argument('--start-primal',type=Path)
    p.add_argument('--digits',type=int,default=10)
    p.add_argument('--resume',action='store_true',help='Restore saved PSD cuts and working columns')
    p.add_argument('--max-cuts',type=int,default=0,
                   help='Aggregate older cuts into their dual PSD matrices above this pool size')
    p.add_argument('--keep-recent',type=int,default=700)
    p.add_argument('--price-every',type=int,default=1)
    p.add_argument('--lp-solver',choices=['simplex','ipm'],default='simplex')
    args=p.parse_args()
    if min(args.rounds,args.tolerance,args.eigen_tolerance,args.cuts_per_block,
           args.lp_seconds,args.digits,args.check_every,args.price_every,args.add_columns,
           args.keep_recent)<=0 or args.margin<0 or args.columns<0 or args.max_cuts<0:
        p.error('Invalid numerical limits')
    data=json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states,restrictions,states6=archive['states'],archive['restrictions'],archive['states6']
    rebuilt,restrictions2,states62,meta=enumerate_seven(data,max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states,rebuilt)
            or not np.array_equal(restrictions,restrictions2) or not np.array_equal(states6,states62)):
        raise ValueError('Archive failed complete cover re-enumeration')
    certificate=json.loads(args.certificate.read_text())
    if certificate.get('format_version') != 2:
        raise ValueError('Use expanded_sdp7.py for certificates with extra PSD blocks')
    verify(data,states,restrictions,certificate)
    saved_certificate=args.output_dir/'certificate.json'
    if saved_certificate.exists():
        previous=json.loads(saved_certificate.read_text())
        verify(data,states,restrictions,previous)
        if Fraction(previous['exact_bound'])<Fraction(certificate['exact_bound']):
            certificate=previous
    patterns,objective6,blocks=assemble(data)
    if (len(blocks)!=len(certificate['inherited']['blocks'])
            or any(json.loads(json.dumps(b['flags']))!=saved['flags']
                   for b,saved in zip(blocks,certificate['inherited']['blocks']))):
        raise ValueError('Certificate flag basis mismatch')
    state_count=certificate['root_state_count']
    root=root_block(states,state_count)
    objective=objective6[restrictions].mean(axis=1)
    templates=blocks+[root]
    seed_matrices=certificate_matrices(certificate)
    args.output_dir.mkdir(parents=True,exist_ok=True)
    best=Fraction(certificate['exact_bound'])
    best_certificate=certificate
    save(args.output_dir/'certificate.json',certificate)
    initial_check=verify(data,states,restrictions,certificate)
    initial_check.update(complete_cover_reenumerated=True,
                         coverage=meta['meaning']+'; complete cover re-enumerated')
    save(args.output_dir/'verification.json',initial_check)
    cut_matrices=[]
    cut_rows=[]
    cut_factors=[]

    def add_cut(block_index,matrix,factor=None):
        norm=np.linalg.norm(matrix)
        if norm<1e-25:
            return
        matrix=matrix/norm
        if factor is None:
            eig,vec=np.linalg.eigh((matrix+matrix.T)/2)
            factor=vec*np.sqrt(np.maximum(eig,0))
        else:
            factor=factor/np.sqrt(norm)
        if block_index<len(blocks):
            coefficients=block_score(blocks[block_index],matrix)[restrictions].mean(axis=1)
        else:
            coefficients=block_score(root,matrix)
        cut_matrices.append((block_index,matrix))
        cut_factors.append((block_index,factor))
        cut_rows.append(sparse.csr_matrix(coefficients[None,:]))

    # These PSD cuts contain the current dual certificate in their cone, so
    # their full-cover LP should already have an objective near its bound.
    for i,q in enumerate(seed_matrices):
        eigenvalues,vectors=np.linalg.eigh((q+q.T)/2)
        add_cut(i,(vectors*np.maximum(eigenvalues,0)) @ vectors.T)
    history=[]
    if args.columns:
        initial=scores(objective6,blocks,seed_matrices[:-1])[restrictions].mean(axis=1)
        initial+=root_scores(states,seed_matrices[-1],state_count)
        columns=set(np.argsort(initial)[-args.columns:].tolist())
        columns.update(np.random.default_rng(119).choice(len(states),min(400,len(states)),replace=False).tolist())
        # Ensure each available flag has a positive diagonal in some selected
        # column; otherwise margin maximization can get stuck at zero solely
        # because that flag has not yet appeared in the working columns.
        for block in templates:
            counts=block['counts'].tocsr()
            for j,(a,b) in enumerate(block['pairs']):
                if a!=b:
                    continue
                vector=counts.getrow(j).toarray().ravel()
                if block is not root:
                    vector=vector[restrictions].mean(axis=1)
                if float(np.max(vector))>0:
                    columns.add(int(np.argmax(vector)))
        empty6=data['patterns'].index('-'*len(data['tuples']))
        columns.update(np.flatnonzero(np.all(restrictions==empty6,axis=1)).tolist())
        if args.start_primal:
            with np.load(args.start_primal) as saved:
                columns.update(int(i) for i in saved['indices'])
        active=np.array(sorted(columns),dtype=np.int64)
    else:
        active=np.arange(len(states))

    checkpoint=args.output_dir/'checkpoint.npz'
    cover_digest=hashlib.sha256(states.tobytes()+restrictions.tobytes()).hexdigest()
    round_offset=0
    if args.resume and checkpoint.exists():
        with np.load(checkpoint) as saved:
            if str(saved['cover_digest'])!=cover_digest:
                raise ValueError('Checkpoint cover mismatch')
            cut_matrices.clear();cut_rows.clear();cut_factors.clear()
            offsets=saved['offsets'];flat=saved['factors']
            for j,(block_index,width) in enumerate(zip(saved['blocks'],saved['widths'])):
                i=int(block_index)
                factor=flat[int(offsets[j]):int(offsets[j+1])].reshape(len(templates[i]['flags']),int(width))
                add_cut(i,factor @ factor.T,factor=factor)
            active=saved['active'].astype(np.int64)
            round_offset=int(saved['round'])
        report_path=args.output_dir/'report.json'
        if report_path.exists():
            history=json.loads(report_path.read_text()).get('history',[])
        # A newer incumbent may be stronger than the certificate used when
        # the checkpoint was written. Keep its PSD matrices in the cut cone.
        for i,q in enumerate(seed_matrices):
            eig,vec=np.linalg.eigh((q+q.T)/2)
            add_cut(i,(vec*np.maximum(eig,0)) @ vec.T)
    elif args.start_primal:
        # Import the near-feasible moment eigenbasis, not just its row support.
        with np.load(args.start_primal) as saved:
            initial_weights=np.zeros(len(states))
            initial_weights[saved['indices']]=saved['weights']
        for i,q in enumerate(moments(blocks,root,restrictions,initial_weights)):
            _,vectors=np.linalg.eigh((q+q.T)/2)
            for j in range(len(vectors)):
                vector=vectors[:,j:j+1]
                add_cut(i,vector @ vector.T,factor=vector)

    def save_checkpoint(round_number):
        widths=[factor.shape[1] for _,factor in cut_factors]
        sizes=[factor.size for _,factor in cut_factors]
        temporary=args.output_dir/'checkpoint.tmp.npz'
        np.savez_compressed(temporary,blocks=np.array([i for i,_ in cut_factors]),
             widths=np.array(widths),offsets=np.cumsum([0]+sizes),
             factors=np.concatenate([factor.ravel() for _,factor in cut_factors]),
             active=active,round=round_number,cover_digest=cover_digest,
             indices=support,weights=weights[support])
        temporary.replace(checkpoint)

    def make_lp():
        if args.feasibility:
            return FeasibilityLP(objective[active],args.lp_seconds,float(best)-.8*args.tolerance)
        return IncrementalLP(objective[active],args.lp_seconds,args.lp_solver) if args.incremental else None

    lp=make_lp()
    tick=time.monotonic()
    print(json.dumps(dict(baseline=float(best),patterns=len(states),initial_cuts=len(cut_rows))),flush=True)
    for iteration in range(args.rounds):
        working_rows=cut_rows if len(active)==len(states) else [row[:,active] for row in cut_rows]
        rhs=np.array([-args.margin*np.trace(q) for _,q in cut_matrices])
        lp_tick=time.monotonic()
        if args.feasibility:
            result=lp.solve(working_rows,[float(np.trace(q)) for _,q in cut_matrices],
                            float(best)-.8*args.tolerance)
        else:
            result=lp.solve(working_rows,rhs) if lp else linprog(-objective[active],A_ub=-sparse.vstack(working_rows),b_ub=rhs,
                       A_eq=sparse.csr_matrix(np.ones((1,len(active)))),b_eq=[1.],
                       bounds=(0,None),method=args.method,
                       options=dict(time_limit=args.lp_seconds,primal_feasibility_tolerance=1e-9,
                                    dual_feasibility_tolerance=1e-9,ipm_optimality_tolerance=1e-10))
        if not result.success:
            save(args.output_dir/'report.json',dict(status=str(result.message),
                 certified_upper=str(best),history=history))
            raise RuntimeError(f'LP failed: {result.message}')
        weights=np.zeros(len(states))
        weights[active]=result.x
        moment_matrices=moments(blocks,root,restrictions,weights)
        eigensystems=[np.linalg.eigh((q+q.T)/2) for q in moment_matrices]
        minimum=min(float(eigenvalues[0]) for eigenvalues,_ in eigensystems)
        dual_matrices=[np.zeros_like(q) for q in seed_matrices]
        dual_available=not args.feasibility or result.objective_multiplier>1e-12
        dual_scale=result.objective_multiplier if args.feasibility and dual_available else 1.
        for multiplier,(i,q) in zip(-result.ineqlin.marginals,cut_matrices):
            dual_matrices[i]+=max(0.,float(multiplier))*q/dual_scale
        value=float(objective @ weights)
        # Bound the true unshifted primal with the PSD LP dual matrices.
        numerical_values=scores(objective6,blocks,dual_matrices[:-1])[restrictions].mean(axis=1)
        numerical_values+=root_scores(states,dual_matrices[-1],state_count)
        if not dual_available:
            numerical_values-=objective
        numerical_upper=float(np.max(numerical_values))
        row=dict(round=round_offset+iteration+1,cuts=len(cut_rows),lp_seconds=time.monotonic()-lp_tick,
                 columns=len(active),
                 lp_objective=value,numerical_dual_upper=numerical_upper,
                 minimum_moment_eigenvalue=minimum,margin=args.margin,
                 positive_weights=int(sum(weights>1e-10)),seconds=time.monotonic()-tick)
        if args.feasibility:
            row.update(candidate_margin=result.gamma,target=float(best)-.8*args.tolerance,
                       objective_multiplier=result.objective_multiplier)
        if dual_available and (numerical_upper<float(best)-1e-6 or (iteration+1)%args.check_every==0
                or iteration==args.rounds-1 or minimum>0):
            bound,cert=exact_certificate(patterns,blocks,dual_matrices,states,restrictions,
                                         state_count,digits=args.digits)
            cert.update(coefficient=data['coefficient'],summands=2,tuples=data['tuples'],
                        cover6=str(args.cover6),cover7=str(args.cover7),
                        search='Convex full-cover eigenvector-cut LP dual')
            if bound<best:
                checked=verify(data,states,restrictions,cert)
                checked.update(complete_cover_reenumerated=True,
                               coverage=meta['meaning']+'; complete cover re-enumerated')
                save(args.output_dir/'certificate.json',cert)
                save(args.output_dir/'verification.json',checked)
                best,best_certificate=bound,cert
        support=np.flatnonzero(weights>0)
        temporary=args.output_dir/'primal.tmp.npz'
        np.savez_compressed(temporary,indices=support,weights=weights[support])
        temporary.replace(args.output_dir/'primal.npz')
        row.update(certified_upper=str(best),certified_upper_decimal=float(best),
                   numerical_gap=float(best)-value,
                   primal_lower_certified=False)
        if minimum>0 and float(best)-value<2*args.tolerance:
            from verify_primal_sdp7 import verify_primal
            integers=[max(0,int(round(float(weights[i])*10**15))) for i in support]
            try:
                checked=verify_primal(data,states,restrictions,best_certificate,
                                      support.tolist(),integers)
                save(args.output_dir/'primal_certificate.json',dict(coefficient=data['coefficient'],
                     indices=support.tolist(),weight_numerators=integers))
                save(args.output_dir/'optimality_verification.json',checked)
                row.update(primal_lower_certified=True,certified_lower=checked['exact_lower'],
                           certified_gap=checked['exact_gap'],certified_gap_decimal=checked['gap'])
            except ValueError as exc:
                row['primal_exact_check_failure']=str(exc)
        history.append(row)
        print(json.dumps(row),flush=True)
        save(args.output_dir/'report.json',dict(method='Convex full-cover eigenvector-cut outer approximation',
             certified_upper=str(best),certified_upper_decimal=float(best),
             primal_lower_certified=row['primal_lower_certified'],tolerance=args.tolerance,
             checkpoint=str(checkpoint),cover6=str(args.cover6),cover7=str(args.cover7),
             configuration=dict(feasibility=args.feasibility,incremental=args.incremental,
                                columns=args.columns,add_columns=args.add_columns,
                                eigen_tolerance=args.eigen_tolerance,lp_seconds=args.lp_seconds),
             history=history))
        if row.get('primal_lower_certified') and row['certified_gap_decimal']<=args.tolerance:
            save_checkpoint(round_offset+iteration+1)
            break
        new_columns=np.array([],dtype=np.int64)
        if len(active)<len(states) and ((iteration+1)%args.price_every==0 or not dual_available):
            missing=np.ones(len(states),dtype=bool)
            missing[active]=False
            missing &= numerical_values>float(np.max(numerical_values[active]))+1e-8
            violating=np.flatnonzero(missing)
            new_columns=violating[np.argsort(numerical_values[violating])[-args.add_columns:]]
        added=0
        for i,(eigenvalues,vectors) in enumerate(eigensystems):
            required=result.gamma if args.feasibility else args.margin
            negative=np.flatnonzero(eigenvalues<required-args.eigen_tolerance)
            for j in negative[:args.cuts_per_block]:
                vector=vectors[:,j:j+1]
                add_cut(i,vector @ vector.T,factor=vector)
                added+=1
        if not added:
            if len(active)<len(states) and not len(new_columns):
                missing=np.ones(len(states),dtype=bool)
                missing[active]=False
                missing &= numerical_values>float(np.max(numerical_values[active]))+1e-8
                violating=np.flatnonzero(missing)
                new_columns=violating[np.argsort(numerical_values[violating])[-args.add_columns:]]
            if not len(new_columns):
                break
        if len(new_columns):
            active=np.union1d(active,new_columns)
            lp=make_lp()
        if args.max_cuts and len(cut_factors)>args.max_cuts:
            recent=list(cut_factors[-args.keep_recent:])
            cut_matrices.clear();cut_rows.clear();cut_factors.clear()
            # The dual aggregates preserve the just-solved LP dual in the
            # new cone. The incumbent matrices also preserve its global bound.
            for i,q in enumerate(dual_matrices):
                add_cut(i,q)
            for i,q in enumerate(certificate_matrices(best_certificate)):
                add_cut(i,q)
            for i,factor in recent:
                add_cut(i,factor @ factor.T,factor=factor)
            lp=make_lp()
        save_checkpoint(round_offset+iteration+1)


if __name__=='__main__':
    main()
