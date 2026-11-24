"""Sanity check (not part of the proof): semantics of the certificate on raw samples.
For random 4-samples from several laws, compute the win indicator and the flag sums DIRECTLY from the raw
values (ratio colours by comparing x_j/x_i with the cuts, sums by comparing x_a+x_b+x_c with 2x_d), with an
implementation separate from verify.py, and compare with the verifier's exact per-pattern score.
Reports E[win], E[sum <Q,M>] (must be >= 0 up to noise for every law), and E[score] (<= C_BF)."""
import json, random, math
from fractions import Fraction as Fr
from itertools import combinations
import verify
from field_r import K, Field

cover = json.load(open('cover_n4.json')); cert = json.load(open('cert_exact.json'))
cuts = [float(Fr(c)) for c in cover['cuts']]
CBF = 0.40069537232930136
scores = verify.verify(cover, cert, field=Field)
score_of = {P: float(s) for P, s in zip(cover['patterns'], scores)}
ff = [tuple(f) for f in cover['form_order']]
blocks = []
for B in cert['blocks']:
    W = [[float(K(x)) for x in row] for row in B['W']]; Y = [[float(K(x)) for x in row] for row in B['Y']]
    d, k = len(W), len(Y)
    Q = [[sum(W[i][a] * Y[a][b] * W[j][b] for a in range(k) for b in range(k)) for j in range(d)] for i in range(d)]
    blocks.append((B['type'], {(a, tuple(c)): n for n, (a, c) in enumerate(B['flags'])}, Q))


def pair_signs(lo, hi):            # '+' iff hi < cut*lo, for each cut
    return ''.join('+' if hi < c * lo else '-' for c in cuts)


def raw_eval(x):
    x = sorted(x)
    win = (x[0] + x[1] + x[2] < 2 * x[3]) + (x[0] + x[1] + x[3] < 2 * x[2])   # targets 3 and 2
    # pattern string straight from the raw values
    P = ''
    for f in ff:
        if f[0] == 'pair': P += '+' if x[f[2]] < cuts[f[3]] * x[f[1]] else '-'
        else: P += '+' if x[f[1]] + x[f[2]] + x[f[3]] < 2 * x[f[4]] else '-'
    # flag sum for family (2,3): roots = 2 points, extensions = the other two points (ordered)
    tot = 0.0
    for R in combinations(range(4), 2):
        ty = pair_signs(x[R[0]], x[R[1]])
        rest = [i for i in range(4) if i not in R]
        for a, b in ((rest[0], rest[1]), (rest[1], rest[0])):
            def flag(e):
                pts = sorted(R + (e,))
                sub = ''.join(pair_signs(x[pts[i]], x[pts[j]]) for i, j in combinations(range(3), 2))
                return (sub, tuple(pts.index(i) for i in R))
            fa, fb = flag(a), flag(b)
            for bty, idx, Q in blocks:
                if bty == ty and fa in idx and fb in idx: tot += Q[idx[fa]][idx[fb]]
    tot /= 12        # norm = C(4,2)*C(2,1)*C(1,1)
    return win / 4, tot, P


laws = {
    'uniform': lambda: random.random(),
    'exp': lambda: random.expovariate(1),
    'loguniform(-6,0)': lambda: math.exp(random.uniform(-6, 0)),
    'lognormal(0,.4)': lambda: math.exp(random.gauss(0, 0.4)),
    'BF-like r,N=30,eta=1e-3': None,
}
r = 0.474346455454904


def bf_sample(eta=1e-3, N=30, L=6):
    v = 0.0
    for l in range(L):
        if random.random() >= r:   # nonzero digit at this level
            j = 1
            while j < N and random.random() < 0.8: j += 1
            v += (1 - 2.0 ** (-j)) * eta ** l
    return v + eta ** L * random.random()


random.seed(7)
n = 60000
for name, law in laws.items():
    draw = law if law else bf_sample
    sw = sq = ss = 0.0; bad = 0; miss = 0
    for _ in range(n):
        x = [draw() for _ in range(4)]
        if len(set(x)) < 4 or min(x) <= 0: continue
        w, q, P = raw_eval(x)
        if P not in score_of: miss += 1; continue
        sc = score_of[P]
        if abs((w + q) - sc) > 1e-9: bad += 1
        sw += w; sq += q; ss += sc
    print(json.dumps(dict(law=name, samples=n, pattern_missing=miss, raw_vs_verifier_mismatch=bad,
                          E_win=round(sw / n, 5), E_flag_term=round(sq / n, 6), E_score=round(ss / n, 5), C_BF=round(CBF, 5))))
