import os
"""Red controls: perturbed inputs / wrong interpretations must be rejected."""
import json, copy, random
from fractions import Fraction as F
import qr
import verify_indep as V
import cover_indep as C

D = V.D
cover0 = json.load(open(D + 'cover_n4.json'))
cert0 = json.load(open(D + 'cert_exact.json'))


def run(name, **kw):
    try:
        res, scores, S, Qs = V.main(verbose=False, **kw)
        ok = (res['n_violations'] == 0 and all(v[0] for v in res['Y_posdef'].values())
              and res['flags_inconsistent_with_type'] == 0 and res['missing_flags'] == 0)
        print(f'{name:55s} accepted={ok}  viol={res["n_violations"]} tight={res["n_tight"]} '
              f'worst={res["worst_violation"]:.3e} missing={res["missing_flags"]} '
              f'Ypd={[v[0] for v in res["Y_posdef"].values()]}')
    except Exception as e:
        print(f'{name:55s} accepted=False  (exception {type(e).__name__}: {str(e)[:60]})')


random.seed(1)
run('baseline')
run('coefficient order reversed', reverse=True)
run('flag string cut-major', flag_cutmajor=True)

# perturb one Y entry (symmetric) by 2^-40
for bi in range(4):
    c = copy.deepcopy(cert0)
    Y = c['blocks'][bi]['Y']
    i = random.randrange(len(Y)); j = random.randrange(len(Y))
    for (a, b) in {(i, j), (j, i)}:
        Y[a][b][0] = str(F(Y[a][b][0]) + F(1, 2**40))
    run(f'Y[{bi}][{i},{j}] += 2^-40 (sym)', cert_override=c)

# perturb Y in the direction that scales Q up: Y *= (1+2^-40)
c = copy.deepcopy(cert0)
for b in c['blocks']:
    b['Y'] = [[[str(F(x) * (1 + F(1, 2**40))) for x in el] for el in row] for row in b['Y']]
run('all Y scaled by (1+2^-40)', cert_override=c)
c = copy.deepcopy(cert0)
for b in c['blocks']:
    b['Y'] = [[[str(F(x) * (1 - F(1, 2**40))) for x in el] for el in row] for row in b['Y']]
run('all Y scaled by (1-2^-40)', cert_override=c)

# asymmetric Y
c = copy.deepcopy(cert0)
c['blocks'][1]['Y'][0][1][0] = str(F(c['blocks'][1]['Y'][0][1][0]) + F(1, 2**50))
run('Y asymmetric (one entry +2^-50)', cert_override=c)

# W perturbation
for bi in range(4):
    c = copy.deepcopy(cert0)
    W = c['blocks'][bi]['W']
    i = random.randrange(len(W)); j = random.randrange(len(W[0]))
    W[i][j][1] = str(F(W[i][j][1]) + F(1, 2**30))
    run(f'W[{bi}][{i},{j}] r-coef += 2^-30', cert_override=c)

# swap two flag labels within block
c = copy.deepcopy(cert0)
fl = c['blocks'][0]['flags']; fl[3], fl[4] = fl[4], fl[3]
run('block0: swap flags 3 and 4', cert_override=c)
c = copy.deepcopy(cert0)
fl = c['blocks'][2]['flags']; fl[0], fl[5] = fl[5], fl[0]
run('block2: swap flags 0 and 5', cert_override=c)
# swap block types
c = copy.deepcopy(cert0)
c['blocks'][1]['type'], c['blocks'][2]['type'] = c['blocks'][2]['type'], c['blocks'][1]['type']
run('swap types of blocks 1,2', cert_override=c)
# drop a block
c = copy.deepcopy(cert0)
c['blocks'] = c['blocks'][:3]
run('drop block 3', cert_override=c)
# add an extra pattern (unrealizable but tests score): obj 1/2 cluster
cv = copy.deepcopy(cover0)
cv['patterns'] = cv['patterns'] + ['++++++++++++++++++++']
run('add pattern ++..++ (both win, cluster)', cover_override=cv)

# lower the bound: compare with CBF - 1e-30
saved = V.CBF
V.CBF = qr.sub(saved, qr.make([F(1, 10**30), 0, 0, 0]))
run('bound lowered to CBF - 1e-30')
V.CBF = qr.make([F(4007, 10000), 0, 0, 0])
run('bound replaced by rational 0.4007 (> CBF)')
V.CBF = qr.make([F(40069537, 10**8), 0, 0, 0])
run('bound replaced by rational 0.40069537 (< CBF)')
V.CBF = saved

# cover controls
print('--- cover controls')
pr = copy.deepcopy(cover0['pruned'])
k = random.choice(list(pr)); kk = list(pr[k])[0]
pr[k][kk] = str(-F(pr[k][kk]))
print('negated one Farkas weight -> failures:', len(C.check_farkas('plus_neg', pr)))
pr = copy.deepcopy(cover0['pruned'])
k = [p for p in pr if len(pr[p]) >= 2][5]
del pr[k][list(pr[k])[0]]
print('deleted one weight from', k, '-> failures:', len(C.check_farkas('plus_neg', pr)))
pats = list(cover0['patterns']); dropped = pats.pop(17)
print('dropped retained pattern -> partition problems:', C.check_partition(pats, cover0['pruned'])[:2])
pr = dict(cover0['pruned']); k = random.choice(list(pr)); del pr[k]
print('dropped pruned prefix -> partition problems:', C.check_partition(cover0['patterns'], pr)[:2])
pr = dict(cover0['pruned']); pr['+-'] = {'0': '1'}
print('added overlapping prefix +- -> partition problems:', C.check_partition(cover0['patterns'], pr)[:2])
# change a cut: 7/6 -> 6/5 (realizable set should change)
saved = C.cuts[:]
C.cuts[0] = F(6, 5)
C.FX[:] = [C.form_vec_x(f) for f in C.forms]; C.FG[:] = [C.to_gaps(v) for v in C.FX]
print('cut 7/6 -> 6/5: Farkas failures', len(C.check_farkas('plus_neg')))
C.cuts[:] = saved
C.FX[:] = [C.form_vec_x(f) for f in C.forms]; C.FG[:] = [C.to_gaps(v) for v in C.FX]

# FM sanity: FM must call every witness-feasible node feasible
real = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'realizable_n4.json')))
nbad = 0
for s in real:
    for l in range(0, 21, 4):
        if C.fm_infeasible(C.constraints(s[:l])):
            nbad += 1
print('FM wrongly infeasible on realizable prefixes:', nbad)
# FM must call every pruned prefix infeasible
nbad = sum(1 for p in cover0['pruned'] if not C.fm_infeasible(C.constraints(p)))
print('FM feasible on a pruned prefix:', nbad)
