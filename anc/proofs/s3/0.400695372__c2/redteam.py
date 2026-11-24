"""Red controls: corrupted certificates and covers must be rejected by verify.py (stdlib only)."""
import json, copy, sys
from fractions import Fraction as Fr
import verify
from field_r import K

cover = json.load(open('cover_n4.json'))
cert3 = json.load(open('cert_exact.json'))
cert2 = json.load(open('cert_stage2.json'))
results = []


def expect_reject(name, fn):
    try:
        fn()
    except (AssertionError, ArithmeticError) as e:
        results.append((name, 'REJECTED', str(e)[:80])); return
    results.append((name, 'ACCEPTED (BAD)', ''))


def expect_accept(name, fn):
    try:
        out = fn()
    except Exception as e:
        results.append((name, 'REJECTED (BAD)', str(e)[:80])); return
    results.append((name, 'accepted', str(out)[:80]))


def add_to_Y(c, b, i, j, delta):
    c = copy.deepcopy(c); B = c['blocks'][b]
    for (u, v) in {(i, j), (j, i)}:
        B['Y'][u][v] = (K(B['Y'][u][v]) + K(delta)).json()
    return c


expect_accept('stage3 original', lambda: verify.stage3_report(cover, cert3)['tight_exact_zero_slack'])
expect_accept('stage2 original', lambda: verify.stage2_report(cover, cert2)['bound_float'])
# Gram / Y perturbations (stage 3): only entries that some tight pattern's score depends on are informative
# (the tight system has rank 10; most Y entries only move non-tight patterns, which have slack >= 0.0224,
#  and such perturbed certificates are still valid proofs).
from math import comb
ff = [tuple(f) for f in cover['form_order']]
obj_, fp_ = verify.pattern_tools(ff, len(cover['cuts']))
tight = cert3['tight_patterns']
def sensitive_entry(b, want_zero=False):
    B = cert3['blocks'][b]; W = [[float(K(x)) for x in row] for row in B['W']]; k = len(B['Y'])
    idx = {(a, tuple(c)): n for n, (a, c) in enumerate(B['flags'])}
    best = (0, None, None); dep = {}
    for P in tight:
        M = {}
        for (fa, fb), c in fp_(P, B['t'], B['f'], B['type']).items():
            if fa in idx and fb in idx: M[(idx[fa], idx[fb])] = M.get((idx[fa], idx[fb]), 0) + c
        for i in range(k):
            for j in range(i, k):
                g = sum(c * (W[u][i] * W[v][j] + W[u][j] * W[v][i]) for (u, v), c in M.items()) / (2 if i == j else 1)
                dep[(i, j)] = max(dep.get((i, j), 0), abs(g))
                if abs(g) > abs(best[0]): best = (g, (i, j), P)
    if want_zero: return next(e for e, v in sorted(dep.items()) if v == 0)
    return best
for b in range(len(cert3['blocks'])):
    g, (i, j), P = sensitive_entry(b)
    sgn = 1 if g > 0 else -1
    for delta, label in ((Fr(sgn, 10**12), 'raises a tight score'), (Fr(-sgn, 10**12), 'lowers a tight score')):
        expect_reject(f'block{b} Y[{i},{j}] 1e-12, {label}',
                      lambda b=b, i=i, j=j, delta=delta: verify.stage3_report(cover, add_to_Y(cert3, b, i, j, delta)))
    (i0, j0) = sensitive_entry(b, want_zero=True)
    for d0 in (Fr(1, 10**12), Fr(-1, 10**12)):
        expect_accept(f'block{b} Y[{i0},{j0}] {float(d0):+.0e} (no tight dependence: still a valid proof)',
                      lambda b=b, i0=i0, j0=j0, d0=d0: verify.stage3_report(cover, add_to_Y(cert3, b, i0, j0, d0))['tight_exact_zero_slack'])
# Y not positive definite
def nonpd():
    c = copy.deepcopy(cert3); c['blocks'][0]['Y'][0][0] = K(-1).json(); return verify.stage3_report(cover, c)
expect_reject('Y[0][0,0] = -1 (not PD)', nonpd)
# asymmetric Y
def asym():
    c = copy.deepcopy(cert3); c['blocks'][1]['Y'][0][1] = (K(c['blocks'][1]['Y'][0][1]) + K(Fr(1, 10**15))).json()
    return verify.stage3_report(cover, c)
expect_reject('Y asymmetric by 1e-15', asym)
# W perturbation
def wpert():
    c = copy.deepcopy(cert3); B = c['blocks'][2]
    for i in range(len(B['W'])):          # every flag row: shift its first face coordinate
        B['W'][i][0] = (K(B['W'][i][0]) + K(Fr(1, 10**12))).json()
    return verify.stage3_report(cover, c)
expect_reject('W column 0 shifted by 1e-12 on all flags', wpert)
# flags relabelled (swap two flags)
def swapflags():
    c = copy.deepcopy(cert3); B = c['blocks'][3]; B['flags'][0], B['flags'][1] = B['flags'][1], B['flags'][0]
    return verify.stage3_report(cover, c)
expect_reject('two flags swapped', swapflags)
# drop a block
def dropblock():
    c = copy.deepcopy(cert3); c['blocks'].pop(1); return verify.stage3_report(cover, c)
expect_reject('block dropped', dropblock)
# cover corruptions
def drop_excl():
    c = copy.deepcopy(cover); k = next(iter(c['pruned'])); c['pruned'].pop(k); return verify.check_cover(c)
expect_reject('one exclusion removed (gap)', drop_excl)
def bad_weight():
    c = copy.deepcopy(cover)
    for k, w in c['pruned'].items():
        if len(w) >= 2:
            i = next(iter(w)); w[i] = str(Fr(w[i]) * 3); break
    return verify.check_cover(c)
expect_reject('exclusion weight tripled', bad_weight)
def neg_weight():
    c = copy.deepcopy(cover); k = next(iter(c['pruned'])); i = next(iter(c['pruned'][k])); c['pruned'][k][i] = '-1'
    return verify.check_cover(c)
expect_reject('negative exclusion weight', neg_weight)
def drop_pattern():
    c = copy.deepcopy(cover); c['patterns'].pop(0); return verify.check_cover(c)
expect_reject('one retained pattern removed (gap)', drop_pattern)
def flip_pattern():
    c = copy.deepcopy(cover); p = c['patterns'][5]; c['patterns'][5] = p[:-1] + ('+' if p[-1] == '-' else '-')
    return verify.check_cover(c)
expect_reject('one pattern sign flipped', flip_pattern)
def other_cut():
    c = copy.deepcopy(cover); c['cuts'][0] = '6/5'; return verify.check_cover(c)
expect_reject('cut 7/6 -> 6/5 in the cover', other_cut)
def cut_mismatch():
    c = copy.deepcopy(cert3); c['cuts'][0] = '6/5'; return verify.stage3_report(cover, c)
expect_reject('certificate cuts differ from cover', cut_mismatch)
# lower target: claimed value below C_BF must fail
def below():
    from field_r import R
    scores = verify.verify(cover, cert3, field=__import__('field_r').Field)
    target = (R**3 - 6 * R**2 + 6 * R) / 4 - K(Fr(1, 10**30))
    assert all(s <= target for s in scores), 'some pattern above C_BF - 1e-30'
expect_reject('bound C_BF - 1e-30', below)
# stage 2 perturbations
def l_pert(delta):
    def f():
        c = copy.deepcopy(cert2); c['blocks'][2]['L'][0][0] += delta; return verify.stage2_report(cover, c)
    return f
expect_reject('stage2 L[0][0] +1 unit (claimed bound changes)', l_pert(1))
expect_reject('stage2 L[0][0] -1 unit (claimed bound changes)', l_pert(-1))
def l_noclaim():
    c = copy.deepcopy(cert2); c['blocks'][2]['L'][0][0] += 2**30; c.pop('bound')
    out = verify.stage2_report(cover, c); assert out['excess_over_CBF_upper'] < 1e-9, 'excess %.3g' % out['excess_over_CBF_upper']
expect_reject('stage2 L[0][0] + 2^30 units, eps <= 1e-9 test', l_noclaim)
def claim_lower():
    c = copy.deepcopy(cert2); c['bound'] = str(Fr(c['bound']) - Fr(1, 10**20)); return verify.stage2_report(cover, c)
expect_reject('stage2 claimed bound lowered 1e-20', claim_lower)

for r in results: print('%-50s %-16s %s' % r)
bad = [r for r in results if 'BAD' in r[1]]
print('ALL CONTROLS BEHAVED' if not bad else 'CONTROL FAILURES: %d' % len(bad))
