"""Exact arithmetic in a real number field Q(u), u = the unique root of p in an
open rational interval.  Written from scratch for the independent check.

Elements: lists of Fractions [a0, a1, ..., a_{n-1}] meaning sum a_k u^k.
Sign decisions: mean-value enclosure at the midpoint of a rigorously isolated
root interval (Sturm), refined by exact bisection until decided; zero test is
exact (p certified irreducible by a Rabin test mod a prime, else gcd test).
"""
from fractions import Fraction as F
import random

# ---------------------------------------------------------------- polynomials over Q
def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def psub(a, b):
    return padd(a, [-x for x in b])

def pmul(a, b):
    if not a or not b:
        return []
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                r[i + j] += x * y
    return trim(r)

def pdivmod(a, b):
    a = trim(a); b = trim(b)
    assert b, "division by zero polynomial"
    q = [F(0)] * max(len(a) - len(b) + 1, 1)
    r = list(a)
    while len(r) >= len(b) and r:
        c = F(r[-1]) / b[-1]
        k = len(r) - len(b)
        q[k] = c
        for i, y in enumerate(b):
            r[i + k] -= c * y
        r = trim(r)
    return trim(q), r

def pmod(a, b):
    return pdivmod(a, b)[1]

def pgcd(a, b):
    a = trim(a); b = trim(b)
    while b:
        a, b = b, pmod(a, b)
    if not a:
        return []
    lc = a[-1]
    return [x / lc for x in a]

def pderiv(a):
    return trim([i * a[i] for i in range(1, len(a))])

def peval(a, x):
    r = F(0)
    for c in reversed(a):
        r = r * x + c
    return r

def sgn(x):
    return (x > 0) - (x < 0)

def _sign_a_b_sqrt(A, B, D):
    sa, sb = sgn(A), sgn(B)
    if sa >= 0 and sb >= 0:
        return 1 if (sa or sb) else 0
    if sa <= 0 and sb <= 0:
        return -1
    # opposite signs
    c = A * A - B * B * D
    return sa if c > 0 else (sb if c < 0 else 0)

def sturm_count(p, lo, hi):
    """number of distinct real roots of p in (lo, hi], via Sturm."""
    seq = [trim(p), pderiv(p)]
    while seq[-1]:
        r = pmod(seq[-2], seq[-1])
        seq.append([-x for x in r])
    seq = [s for s in seq if s]
    def V(x):
        vals = [sgn(peval(s, x)) for s in seq]
        vals = [v for v in vals if v]
        return sum(1 for i in range(len(vals) - 1) if vals[i] != vals[i + 1])
    return V(lo) - V(hi)

# ---------------------------------------------------------------- irreducibility (Rabin over F_q)
def _ppoly_mod(a, f, q):
    # a, f integer lists mod q, f monic
    a = [x % q for x in a]
    n = len(f) - 1
    while len(a) > n:
        c = a[-1]
        if c:
            k = len(a) - 1 - n
            for i in range(n + 1):
                a[k + i] = (a[k + i] - c * f[i]) % q
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return a

def _pmulq(a, b, f, q):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return _ppoly_mod(r, f, q)

def _powx(e, f, q):
    res = [1]; base = _ppoly_mod([0, 1], f, q)
    while e:
        if e & 1:
            res = _pmulq(res, base, f, q)
        base = _pmulq(base, base, f, q)
        e >>= 1
    return res

def _gcdq(a, b, q):
    def tr(x):
        x = [v % q for v in x]
        while x and x[-1] == 0:
            x.pop()
        return x
    a = tr(a); b = tr(b)
    while b:
        inv = pow(b[-1], q - 2, q)
        r = list(a)
        while len(r) >= len(b) and r:
            c = r[-1] * inv % q
            k = len(r) - len(b)
            for i, y in enumerate(b):
                r[k + i] = (r[k + i] - c * y) % q
            r = tr(r)
        a, b = b, r
    return a

def _primes(lo, hi):
    out = []
    for n in range(max(lo, 2), hi):
        if all(n % d for d in range(2, int(n ** 0.5) + 1)):
            out.append(n)
    return out

def rabin_irreducible_mod(pint, q):
    n = len(pint) - 1
    lc = pint[-1] % q
    if lc == 0:
        return False
    inv = pow(lc, q - 2, q)
    f = [(c * inv) % q for c in pint]
    # x^(q^n) == x mod f
    def xpow_qk(k):
        r = _ppoly_mod([0, 1], f, q)
        for _ in range(k):
            # r <- r^q
            res = [1]; base = r; e = q
            while e:
                if e & 1:
                    res = _pmulq(res, base, f, q)
                base = _pmulq(base, base, f, q)
                e >>= 1
            r = res
        return r
    xq = xpow_qk(n)
    h = xq + [0] * 3
    h[1] -= 1
    if _ppoly_mod(h, f, q):
        return False
    rs = {r for r in range(2, n + 1) if n % r == 0 and all(r % d for d in range(2, r))}
    for r in rs:
        h = xpow_qk(n // r)
        h = (h + [0] * 3)
        h[1] -= 1
        g = _gcdq(h, f, q)
        if len(g) > 1:
            return False
    return True

def certify_irreducible(p, maxprime=3000):
    """p: list of Fractions/ints. Returns a prime q such that p mod q is
    irreducible of full degree (=> p irreducible over Q), or None."""
    from math import lcm, gcd
    den = 1
    for c in p:
        den = lcm(den, F(c).denominator)
    pint = [int(F(c) * den) for c in p]
    g = 0
    for c in pint:
        g = gcd(g, c)
    pint = [c // g for c in pint]
    if len(pint) == 2:
        return 1  # linear
    for q in _primes(3, maxprime):
        if pint[-1] % q == 0:
            continue
        if rabin_irreducible_mod(pint, q):
            return q
    return None

# ---------------------------------------------------------------- the field
class NumberField:
    def __init__(self, poly, interval, name="u"):
        self.p = trim([F(c) for c in poly])
        self.n = len(self.p) - 1
        self.name = name
        lo, hi = F(interval[0]), F(interval[1])
        assert lo < hi
        assert peval(self.p, lo) != 0 and peval(self.p, hi) != 0, "endpoint is a root"
        cnt = sturm_count(self.p, lo, hi)
        self.root_count = cnt
        assert cnt == 1, f"p has {cnt} roots in ({lo},{hi})"
        self.lo, self.hi = lo, hi
        self.slo = sgn(peval(self.p, lo))
        self.irred_prime = certify_irreducible(self.p) if self.n > 1 else 1
        # reduction table: u^k for k = n .. 2n-2 as vectors
        n = self.n
        self.red = {}
        lc = self.p[-1]
        base = [-c / lc for c in self.p[:-1]]  # u^n
        cur = base
        for k in range(n, 2 * n - 1):
            self.red[k] = cur
            # multiply by u
            nxt = [F(0)] + cur[:-1]
            top = cur[-1]
            if top:
                nxt = [a + top * b for a, b in zip(nxt, base)]
            cur = nxt
        self.refine(200)

    # ---- root interval
    def refine(self, bits):
        target = F(1, 2 ** bits)
        while self.hi - self.lo > target:
            m = (self.lo + self.hi) / 2
            s = sgn(peval(self.p, m))
            if s == 0:
                self.lo = self.hi = m
                return
            if s == self.slo:
                self.lo = m
            else:
                self.hi = m

    # ---- element construction
    def elem(self, coeffs):
        if isinstance(coeffs, (str, int, F)):
            coeffs = [coeffs]
        v = [F(c) for c in coeffs]
        assert len(v) <= self.n, (len(v), self.n)
        return v + [F(0)] * (self.n - len(v))

    def zero(self):
        return [F(0)] * self.n

    def one(self):
        return self.elem([1])

    def gen(self):
        return self.elem([0, 1]) if self.n > 1 else self.elem([self.lo])

    def add(self, a, b):
        return [x + y for x, y in zip(a, b)]

    def sub(self, a, b):
        return [x - y for x, y in zip(a, b)]

    def neg(self, a):
        return [-x for x in a]

    def scale(self, a, r):
        return [x * r for x in a]

    def is_rational(self, a):
        return all(x == 0 for x in a[1:])

    def mul(self, a, b):
        n = self.n
        ra = self.is_rational(a); rb = self.is_rational(b)
        if ra:
            return [a[0] * y for y in b]
        if rb:
            return [x * b[0] for x in a]
        prod = [F(0)] * (2 * n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        prod[i + j] += x * y
        res = prod[:n]
        for k in range(n, 2 * n - 1):
            c = prod[k]
            if c:
                res = [r + c * t for r, t in zip(res, self.red[k])]
        return res

    def inv(self, a):
        assert self.irred_prime, "inverse needs irreducible modulus"
        if self.n == 1:
            return [1 / a[0]]
        # extended Euclid: s*a + t*p = g (const)
        r0, r1 = trim(self.p), trim(a)
        s0, s1 = [], [F(1)]
        while len(r1) > 1:
            q, r = pdivmod(r0, r1)
            r0, r1 = r1, r
            s0, s1 = s1, psub(s0, pmul(q, s1))
        assert r1, "not invertible"
        c = r1[0]
        s = pmod(s1, self.p)
        s = [x / c for x in s]
        return s + [F(0)] * (self.n - len(s))

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    # ---- evaluation / sign
    def _enclose(self, a):
        """rational midpoint value and rigorous error radius."""
        m = (self.lo + self.hi) / 2
        r = (self.hi - self.lo) / 2
        val = peval(a, m)
        X = max(abs(self.lo), abs(self.hi))
        B = F(0)
        Xk = F(1)
        for k in range(1, len(a)):
            B += k * abs(a[k]) * Xk
            Xk *= X
        return val, B * r

    def is_zero_exact(self, a):
        if all(x == 0 for x in a):
            return True
        if self.irred_prime:
            return False
        g = pgcd(trim(a), self.p)
        if len(g) <= 1:
            return False
        return sturm_count(g, self.lo, self.hi) >= 1

    def sign(self, a, maxbits=20000):
        if all(x == 0 for x in a):
            return 0
        if self.is_rational(a):
            return sgn(a[0])
        if self.n == 2:
            return self._sign_quadratic(a)
        if self.is_zero_exact(a):
            return 0
        bits = 200
        while True:
            val, err = self._enclose(a)
            if abs(val) > err:
                return sgn(val)
            bits *= 2
            if bits > maxbits:
                raise RuntimeError("sign undecided")
            self.refine(bits)

    def _sign_quadratic(self, a):
        # exact: u = (-p1 + eps*sqrt(D)) / (2 p2), eps = +-1 fixed by the interval
        p0, p1, p2 = self.p
        D = p1 * p1 - 4 * p0 * p2
        if not hasattr(self, '_eps'):
            assert D > 0
            # D must not be a rational square (irreducible) -- checked via irred_prime
            assert self.irred_prime
            m = (self.lo + self.hi) / 2
            # which root lies in the interval: sign of (2 p2 m + p1)
            self._eps = sgn(2 * p2 * m + p1)
            assert self._eps != 0
        A = a[0] - a[1] * p1 / (2 * p2)
        B = self._eps * a[1] / (2 * p2)
        return _sign_a_b_sqrt(A, B, D)

    def approx(self, a):
        val, err = self._enclose(a)
        return val, err

    def to_float(self, a):
        return float(self._enclose(a)[0])

    def __repr__(self):
        return f"NumberField(p={[str(c) for c in self.p]}, root in ({float(self.lo)},{float(self.hi)}))"


def self_test():
    K = NumberField([-2, 0, 1], [1, 2])
    s2 = K.gen()
    assert K.sign(K.sub(K.mul(s2, s2), K.elem([2]))) == 0
    assert K.sign(K.sub(s2, K.elem([F(14142, 10000)]))) == 1
    assert K.sign(K.sub(s2, K.elem([F(14143, 10000)]))) == -1
    assert K.irred_prime
    # reducible modulus: (x^2-2)(x-3): root in (1,2) is sqrt2; zero test by gcd
    K2 = NumberField(pmul([F(-2), F(0), F(1)], [F(-3), F(1)]), [1, 2])
    assert K2.irred_prime is None
    a = K2.elem([-2, 0, 1])  # u^2-2 = 0 at sqrt2 though nonzero poly
    assert K2.sign(a) == 0
    assert K2.sign(K2.elem([-3, 1])) == -1
    inv = K.inv(K.elem([1, 1]))
    assert K.sign(K.sub(K.mul(inv, K.elem([1, 1])), K.one())) == 0
    print("nf self-test ok")

if __name__ == "__main__":
    self_test()
