"""Independent cover checks: forms, partition, Farkas/Gordan exclusions,
exact-LP enumeration of realizable patterns, random exact sampling."""
import json, itertools, random, time
from fractions import Fraction as F
from nf import NumberField, sgn

PAIRS = list(itertools.combinations(range(4), 2))


def load_cover(path):
    d = json.load(open(path))
    if "polynomial" in d:
        K = NumberField(d["polynomial"], d["root_interval"], "g")
    else:
        K = NumberField([-1, 1], [0, 2], "one")  # Q itself
    def parse(v):
        if isinstance(v, str):
            return K.elem([v])
        return K.elem(v)
    c = parse(d["c"])
    cuts = [parse(q) for q in d["cuts"]]
    return d, K, c, cuts, parse


def build_forms(K, c, cuts, npts=4):
    """Return list of (label, coeffs in gap coords d_0..d_{npts-1}) for the
    form ordering: pair forms (i,j) x cuts, then sum forms target 1..3."""
    forms = []
    one = K.one()
    zero = K.zero()
    def x_coef(k, m):  # coefficient of d_m in x_k
        return one if m <= k else zero
    for (i, j) in itertools.combinations(range(npts), 2):
        for qi, q in enumerate(cuts):
            co = [K.sub(x_coef(j, m), K.mul(q, x_coef(i, m))) for m in range(npts)]
            forms.append((("pair", i, j, qi), co))
    if npts == 4:
        for T in (1, 2, 3):
            co = []
            for m in range(npts):
                s = zero
                for o in range(npts):
                    if o != T:
                        s = K.add(s, x_coef(o, m))
                s = K.sub(s, K.mul(c, x_coef(T, m)))
                co.append(s)
            forms.append((("sum", T), co))
    return forms


def partition_check(patterns, pruned_keys, N):
    allk = list(patterns) + list(pruned_keys)
    res = {}
    res["alphabet_ok"] = all(set(s) <= {"+", "-"} for s in allk)
    res["pattern_len_ok"] = all(len(s) == N for s in patterns)
    res["prefix_len_ok"] = all(1 <= len(s) <= N for s in pruned_keys)
    res["duplicates"] = len(allk) - len(set(allk))
    srt = sorted(set(allk))
    viol = [(a, b) for a, b in zip(srt, srt[1:]) if b.startswith(a)]
    res["prefix_violations"] = len(viol)
    kraft = sum(F(1, 2 ** len(s)) for s in set(allk))
    res["kraft_sum"] = str(kraft)
    res["partition_ok"] = (res["alphabet_ok"] and res["pattern_len_ok"] and res["prefix_len_ok"]
                           and res["duplicates"] == 0 and not viol and kraft == 1)
    return res


def farkas_check(K, forms, prefix, weights, parse):
    """weights: {str(index): value}. Returns (ok, reason)."""
    n = len(forms[0][1])
    tot = [K.zero() for _ in range(n)]
    anypos = False
    for ks, w in weights.items():
        k = int(ks)
        if not (0 <= k < len(prefix)):
            return False, f"weight index {k} outside prefix of length {len(prefix)}"
        w = parse(w)
        s = K.sign(w)
        if s < 0:
            return False, f"negative weight at {k}"
        if s > 0:
            anypos = True
        # signed form g_k < 0 on the cell: '+' -> f_k<0 ; '-' -> -f_k<0
        sig = 1 if prefix[k] == "+" else -1
        co = forms[k][1]
        for m in range(n):
            tot[m] = K.add(tot[m], K.scale(K.mul(w, co[m]), sig))
    if not anypos:
        return False, "no positive weight"
    for m in range(n):
        if K.sign(tot[m]) < 0:
            return False, f"combined coefficient of d{m} is negative"
    return True, ""


def pattern_of_point(K, forms, d):
    """d: gap coordinates (field elements, all > 0). Returns string or None if degenerate."""
    out = []
    for _, co in forms:
        v = K.zero()
        for m in range(len(d)):
            v = K.add(v, K.mul(co[m], d[m]))
        s = K.sign(v)
        if s == 0:
            return None
        out.append("+" if s < 0 else "-")
    return "".join(out)


# ---------------------------------------------------------------- exact LP (condensed tableau, Bland)
def lp_strict(K, rows):
    """rows: list of coefficient vectors G (len 4) meaning constraint G.d < 0.
    Solve max t s.t. G.d + t <= 0, -d_m + t <= 0, sum d <= 1, d,t >= 0.
    Returns (tstar, d) exactly."""
    nv = 5
    A = []
    b = []
    for G in rows:
        A.append(list(G) + [K.one()]); b.append(K.zero())
    for m in range(4):
        r = [K.zero() for _ in range(4)] + [K.one()]
        r[m] = K.elem([-1])
        A.append(r); b.append(K.zero())
    A.append([K.one()] * 4 + [K.zero()]); b.append(K.one())
    nrow = len(A)
    obj = [K.zero()] * 4 + [K.elem([-1])]  # z + sum o_j N_j = z0, maximize t
    z0 = K.zero()
    nonbasic = list(range(nv))
    basic = [nv + i for i in range(nrow)]
    sign = K.sign
    it = 0
    while True:
        it += 1
        cand = [j for j in range(nv) if sign(obj[j]) < 0]
        if not cand:
            break
        s = min(cand, key=lambda j: nonbasic[j])
        best = None
        for i in range(nrow):
            if sign(A[i][s]) > 0:
                ratio = K.div(b[i], A[i][s])
                if best is None:
                    best = (i, ratio)
                else:
                    cmp = sign(K.sub(ratio, best[1]))
                    if cmp < 0 or (cmp == 0 and basic[i] < basic[best[0]]):
                        best = (i, ratio)
        assert best is not None, "unbounded"
        r = best[0]
        p = A[r][s]
        pinv = K.inv(p)
        rowr = [K.mul(x, pinv) for x in A[r]]
        rowr[s] = pinv
        br = K.mul(b[r], pinv)
        for i in range(nrow):
            if i == r:
                continue
            ais = A[i][s]
            if all(x == 0 for x in ais):
                continue
            Ai = A[i]
            for j in range(nv):
                if j == s:
                    continue
                if any(Ai[j]) or any(rowr[j]):
                    Ai[j] = K.sub(Ai[j], K.mul(ais, rowr[j]))
            Ai[s] = K.neg(K.mul(ais, pinv))
            b[i] = K.sub(b[i], K.mul(ais, br))
        os_ = obj[s]
        if any(os_):
            for j in range(nv):
                if j != s:
                    obj[j] = K.sub(obj[j], K.mul(os_, rowr[j]))
            obj[s] = K.neg(K.mul(os_, pinv))
            z0 = K.sub(z0, K.mul(os_, br))
        A[r] = rowr; b[r] = br
        basic[r], nonbasic[s] = nonbasic[s], basic[r]
    val = [K.zero() for _ in range(nv)]
    for i in range(nrow):
        if basic[i] < nv:
            val[basic[i]] = b[i]
    return z0, val[:4]


def signed(K, forms, k, ch):
    co = forms[k][1]
    return co if ch == "+" else [K.neg(x) for x in co]


def enumerate_realizable(K, forms, log=None):
    """DFS over sign prefixes with exact LP; returns {pattern: witness d}."""
    N = len(forms)
    out = {}
    nlp = [0]
    stack = [("", None, [])]
    while stack:
        prefix, w, rows = stack.pop()
        if len(prefix) == N:
            out[prefix] = w
            continue
        k = len(prefix)
        s = None
        if w is not None:
            v = K.zero()
            for m in range(4):
                v = K.add(v, K.mul(forms[k][1][m], w[m]))
            s = K.sign(v)
        for ch in "+-":
            G = signed(K, forms, k, ch)
            nrows = rows + [G]
            if s is not None and s != 0 and ((s < 0) == (ch == "+")):
                stack.append((prefix + ch, w, nrows))
                continue
            nlp[0] += 1
            t, d = lp_strict(K, nrows)
            if K.sign(t) > 0:
                stack.append((prefix + ch, d, nrows))
    return out, nlp[0]


def rational_witness(K, forms, d, pat):
    """Round a field witness to a rational point and re-verify exactly."""
    for bits in (40, 80, 160, 320):
        dr = []
        for x in d:
            v, e = K.approx(x)
            v = F(round(v * 2 ** bits), 2 ** bits)
            dr.append(K.elem([v]))
        if all(K.sign(x) > 0 for x in dr) and pattern_of_point(K, forms, dr) == pat:
            return [str(x[0]) for x in dr]
    return None


def random_points(K, cutsf, cf, count, seed=1):
    """exact rational gap vectors, mixing generic, multi-scale and near-boundary draws."""
    rng = random.Random(seed)
    pts = []
    def rr(lo, hi):
        return F(rng.randint(0, 10 ** 9), 10 ** 9) * (hi - lo) + lo
    specials = [F(q).limit_denominator(10 ** 12) for q in cutsf] + [F(cf).limit_denominator(10 ** 12)]
    for it in range(count):
        mode = it % 4
        x = [F(1)]
        for _ in range(3):
            if mode == 0:
                r = rr(F(1), F(4))
            elif mode == 1:  # near a cut value
                q = rng.choice(specials)
                r = q * (1 + rr(F(-1), F(1)) * F(1, 10 ** rng.randint(3, 12)))
                if r <= 1:
                    r = 1 + F(1, 10 ** 6)
            elif mode == 2:  # multi-scale
                r = rng.choice([rr(F(1), F(3)), rr(F(10), F(1000)), 1 + rr(F(0), F(1, 100))])
            else:
                r = rr(F(1), F(3))
            x.append(x[-1] * r)
        if mode == 3:
            # force a near-tie of a sum form: x_T ~ (sum others)/c
            T = rng.choice([1, 2, 3])
            others = sum(x[o] for o in range(4) if o != T)
            target = others / F(cf).limit_denominator(10 ** 12) * (1 + rr(F(-1), F(1)) * F(1, 10 ** rng.randint(3, 12)))
            x[T] = target
            x = sorted(x)
            if len(set(x)) < 4 or x[0] <= 0:
                continue
        d = [x[0]] + [x[k] - x[k - 1] for k in range(1, 4)]
        if any(v <= 0 for v in d):
            continue
        pts.append([K.elem([v]) for v in d])
    return pts
