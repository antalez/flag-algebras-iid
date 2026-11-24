"""Exact optimal three-point ratio-graph flag certificate (standard library).

Let a=2*sqrt(7)-4 be the positive root of a^2+8*a-12=0.
The one-root two-vertex flags are: lower nonneighbor, lower neighbor,
upper neighbor, upper nonneighbor. Q=a*v*v^T with v=(-t,1,1,0),
t=(sqrt(7)-1)/2. The graph score is J=p_H-p_T.
"""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from itertools import product,combinations
from pathlib import Path
import json
from algebraic_field import make_field


def check():
    F=make_field([-12,8,1]);a=F([0,1]);B=a-1;t=(a+2)/4
    assert a>0 and B>0 and t>0
    v=[-t,F(1),F(1),F(0)]
    Q=[[a*x*y for y in v] for x in v]
    assert Q==[[3*B,-a*t,-a*t,F(0)],[-a*t,a,a,F(0)],[-a*t,a,a,F(0)],[F(0)]*4]
    pairs=list(combinations(range(3),2));rows=[]
    labels={(0,0,0):'0',(1,0,0):'L',(0,0,1):'H',(1,0,1):'P',(1,1,1):'T'}
    for bits in product([0,1],repeat=3):
        if bits[1] and not (bits[0] and bits[2]):continue
        edges=dict(zip(pairs,bits));label=labels[bits]
        def flag(root,other):
            adjacent=edges[tuple(sorted([root,other]))]
            return (1 if adjacent else 0) if other<root else (2 if adjacent else 3)
        flag_term=F(0)
        for root in range(3):
            others=[i for i in range(3) if i!=root]
            flag_term+=Q[flag(root,others[0])][flag(root,others[1])]/3
        objective=F(int(label=='H')-int(label=='T'))
        slack=B-objective-flag_term
        expected=(a/6 if label=='P' else F(0))
        assert slack==expected and slack>=0
        plateau_score=(1+objective+flag_term)/3
        assert plateau_score==(5*a/18 if label=='P' else a/3)
        rows.append(dict(pattern=label,edge_bits=bits,J=int(label=='H')-int(label=='T'),
            flag_term=flag_term.json(),slack=slack.json(),S2_certificate_score=plateau_score.json()))
    assert len(rows)==5
    # Sharpness: an ordered sequence of disjoint cliques of geometric masses.
    q=(4-a)/6;r=1-q
    assert 0<q<1 and q/r==t
    assert 3*B-a*t*t==0
    # The recurrence for the geometric construction has J=B exactly.
    assert B==r**3*B+3*r*q*q-q**3
    V=(1+B)/3
    assert V==a/3
    # Success-probability recurrence for separated-scale positive atoms.
    assert V==r**3*V+q*r*r+2*q*q*r
    return dict(field_polynomial=[-12,8,1],field_generator='a = 2*sqrt(7)-4',
        sample_size=3,root_size=1,flag_size=2,
        flags=['lower nonneighbor','lower neighbor','upper neighbor','upper nonneighbor'],
        positive_multiplier=a.json(),rank_one_vector=[x.json() for x in v],
        J_matrix=[[x.json() for x in row] for row in Q],J_upper=B.json(),
        S2_matrix=[[ (x/3).json() for x in row] for row in Q],S2_upper=V.json(),
        S2_upper_decimal=float(V),pattern_checks=rows,
        extremal_top_mass=q.json(),optimality_verified=True)

if __name__=='__main__':
    result=check();Path(__file__).with_name('first_plateau_flag.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
