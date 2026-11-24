"""Minimal exact arithmetic in Q(sqrt(2)), used for endpoint certificates."""
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Q2:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q2) else Q2(x)

    def __add__(self, other):
        y = self.cast(other)
        return Q2(self.a+y.a, self.b+y.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        y = self.cast(other)
        return Q2(self.a*y.a+2*self.b*y.b, self.a*y.b+self.b*y.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = self.cast(other)
        den = y.a*y.a-2*y.b*y.b
        if not den:
            raise ZeroDivisionError
        return self * Q2(y.a/den, -y.b/den)

    def __bool__(self):
        return bool(self.a or self.b)

    def sign(self):
        a, b = self.a, self.b
        s = lambda x: (x > 0)-(x < 0)
        if not b:
            return s(a)
        if not a:
            return s(b)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        return s(a*a-2*b*b)*(1 if a > 0 else -1)

    def __float__(self):
        return float(self.a)+2**.5*float(self.b)

    def json(self):
        return [str(self.a), str(self.b)]


def solve_linear(a, rhs):
    """Solve an exact possibly overdetermined system; free variables are zero."""
    if not a:
        return []
    n = len(a[0])
    rows = [[Q2.cast(x) for x in row]+[Q2.cast(v)] for row, v in zip(a, rhs)]
    pivots, row = [], 0
    for col in range(n):
        pivot = next((i for i in range(row, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[row], rows[pivot] = rows[pivot], rows[row]
        divisor = rows[row][col]
        rows[row] = [v/divisor for v in rows[row]]
        for i in range(len(rows)):
            if i != row and rows[i][col]:
                multiplier = rows[i][col]
                rows[i] = [x-multiplier*y for x, y in zip(rows[i], rows[row])]
        pivots.append(col)
        row += 1
        if row == len(rows):
            break
    if any(not any(r[:n]) and r[n] for r in rows):
        return None
    result = [Q2()] * n
    for i, col in enumerate(pivots):
        result[col] = rows[i][-1]
    return result
