"""Exact arithmetic in K = Q(r), r the root in (0,1) of r^4 - 4r^3 - 3r^2 - 2r + 2 (irreducible over Q).
Standard library only. Elements are (a0,a1,a2,a3) Fractions meaning a0 + a1 r + a2 r^2 + a3 r^3.
Signs are decided by a rational enclosure of r (bisection, exact polynomial signs), refined until decided;
zero is recognised exactly (all coefficients zero, valid since 1,r,r^2,r^3 are linearly independent over Q).
"""
from fractions import Fraction as Fr
from functools import lru_cache

POLY = (2, -2, -3, -4, 1)            # r^4 = 4r^3 + 3r^2 + 2r - 2
RED = (Fr(-2), Fr(2), Fr(3), Fr(4))  # r^4 expressed in the basis


def _poly(x):
    return x**4 - 4 * x**3 - 3 * x**2 - 2 * x + 2


@lru_cache(None)
def r_enclosure(bits):
    lo, hi = Fr(0), Fr(1)
    assert _poly(lo) > 0 > _poly(hi)          # unique root in (0,1): p' < 0 there
    while hi - lo > Fr(1, 2**bits):
        mid = (lo + hi) / 2
        if _poly(mid) > 0: lo = mid
        else: hi = mid
    assert _poly(lo) > 0 > _poly(hi)
    return lo, hi


def _coef(x):
    if isinstance(x, K): return x.v
    if isinstance(x, (list, tuple)):
        assert len(x) == 4
        return tuple(Fr(v) for v in x)
    return (Fr(x), Fr(0), Fr(0), Fr(0))


@lru_cache(maxsize=None)
def _sign(v):
    if not any(v): return 0
    for bits in (64, 128, 256, 512, 1024, 2048):
        lo, hi = r_enclosure(bits)            # 0 < lo < r < hi < 1, so powers are monotone
        low = v[0] + sum(a * (lo**i if a >= 0 else hi**i) for i, a in enumerate(v[1:], 1))
        up = v[0] + sum(a * (hi**i if a >= 0 else lo**i) for i, a in enumerate(v[1:], 1))
        if low > 0: return 1
        if up < 0: return -1
    raise ArithmeticError('sign undecided')


class K:
    __slots__ = ('v',)
    def __init__(self, x=0): self.v = _coef(x)
    def __add__(self, o): return K(tuple(a + b for a, b in zip(self.v, _coef(o))))
    __radd__ = __add__
    def __neg__(self): return K(tuple(-a for a in self.v))
    def __sub__(self, o): return self + (-K(o))
    def __rsub__(self, o): return K(o) + (-self)
    def __mul__(self, o):
        b = _coef(o); a = self.v
        if not any(b[1:]): return K(tuple(x * b[0] for x in a))
        if not any(a[1:]): return K(tuple(x * a[0] for x in b))
        out = [Fr(0)] * 7
        for i in range(4):
            if a[i]:
                for j in range(4):
                    if b[j]: out[i + j] += a[i] * b[j]
        for d in (6, 5, 4):
            c = out[d]
            if c:
                out[d] = Fr(0)
                for j in range(4): out[d - 4 + j] += c * RED[j]
        return K(tuple(out[:4]))
    __rmul__ = __mul__
    def __truediv__(self, o): return self * inverse(K(o))
    def __rtruediv__(self, o): return K(o) * inverse(self)
    def __pow__(self, n):
        assert type(n) == int and n >= 0
        out = K(1); b = self
        while n:
            if n & 1: out = out * b
            b = b * b; n >>= 1
        return out
    def __bool__(self): return any(self.v)
    def __eq__(self, o): return self.v == _coef(o)
    def __hash__(self): return hash(self.v)
    def sign(self): return _sign(self.v)
    def __lt__(self, o): return _sign((self - K(o)).v) < 0
    def __le__(self, o): return _sign((self - K(o)).v) <= 0
    def __gt__(self, o): return _sign((self - K(o)).v) > 0
    def __ge__(self, o): return _sign((self - K(o)).v) >= 0
    def __float__(self):
        lo, hi = r_enclosure(64); t = float((lo + hi) / 2)
        return sum(float(a) * t**i for i, a in enumerate(self.v))
    def __repr__(self): return 'K(%s)' % ','.join(map(str, self.v))
    def json(self): return [str(a) for a in self.v]
    zero = None


K.zero = K(0)


def parse(x): return K(x)


def inverse(x):
    a = x.v; assert any(a), 'division by zero'
    # matrix of multiplication by x in basis 1,r,r^2,r^3; solve x*y = 1
    cols = [(x * K(tuple(Fr(int(i == j)) for i in range(4)))).v for j in range(4)]
    m = [[cols[j][i] for j in range(4)] + [Fr(int(i == 0))] for i in range(4)]
    for j in range(4):
        p = next(i for i in range(j, 4) if m[i][j] != 0); m[j], m[p] = m[p], m[j]
        pv = m[j][j]; m[j] = [v / pv for v in m[j]]
        for i in range(4):
            if i != j and m[i][j] != 0:
                f = m[i][j]; m[i] = [u - f * w for u, w in zip(m[i], m[j])]
    return K(tuple(m[i][4] for i in range(4)))


R = K((0, 1, 0, 0))
CBF = (R**3 - 6 * R**2 + 6 * R) / 4


class Field:
    """adapter used by verify.field_block"""
    zero = K(0)
    @staticmethod
    def parse(v): return K(v)
