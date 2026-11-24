/-!
# Arithmetic in `Q(r)` and `Z[r]`, `r^4 = 4 r^3 + 3 r^2 + 2 r - 2`

`K`: coefficients of `1, r, r^2, r^3` as rationals.  `Z4`: the same with integers (hot path).
No Mathlib here: this module is compiled to native code.
-/

namespace Fast

structure K where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
deriving Inhabited, BEq, Repr

namespace K

def zero : K := ⟨0, 0, 0, 0⟩
def one : K := ⟨1, 0, 0, 0⟩
def ofRat (q : Rat) : K := ⟨q, 0, 0, 0⟩
def add (x y : K) : K := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def sub (x y : K) : K := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def smul (q : Rat) (x : K) : K := ⟨q * x.a, q * x.b, q * x.c, q * x.d⟩

/-- Product, reduced with `r^4 = -2 + 2r + 3r^2 + 4r^3`, `r^5 = -8 + 6r + 14r^2 + 19r^3`,
`r^6 = -38 + 30r + 63r^2 + 90r^3`. -/
def mul (x y : K) : K :=
  let p0 := x.a * y.a
  let p1 := x.a * y.b + x.b * y.a
  let p2 := x.a * y.c + x.b * y.b + x.c * y.a
  let p3 := x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a
  let p4 := x.b * y.d + x.c * y.c + x.d * y.b
  let p5 := x.c * y.d + x.d * y.c
  let p6 := x.d * y.d
  ⟨p0 - 2 * p4 - 8 * p5 - 38 * p6, p1 + 2 * p4 + 6 * p5 + 30 * p6,
   p2 + 3 * p4 + 14 * p5 + 63 * p6, p3 + 4 * p4 + 19 * p5 + 90 * p6⟩

/-- `B* = (6 r - 6 r^2 + r^3) / 4`. -/
def bstar : K := ⟨0, 3 / 2, -3 / 2, 1 / 4⟩

end K

structure Z4 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving Inhabited, BEq, Repr

namespace Z4

def zero : Z4 := ⟨0, 0, 0, 0⟩
def add (x y : Z4) : Z4 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def sub (x y : Z4) : Z4 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def smul (n : Int) (x : Z4) : Z4 := ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩

def mul (x y : Z4) : Z4 :=
  let p0 := x.a * y.a
  let p1 := x.a * y.b + x.b * y.a
  let p2 := x.a * y.c + x.b * y.b + x.c * y.a
  let p3 := x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a
  let p4 := x.b * y.d + x.c * y.c + x.d * y.b
  let p5 := x.c * y.d + x.d * y.c
  let p6 := x.d * y.d
  ⟨p0 - 2 * p4 - 8 * p5 - 38 * p6, p1 + 2 * p4 + 6 * p5 + 30 * p6,
   p2 + 3 * p4 + 14 * p5 + 63 * p6, p3 + 4 * p4 + 19 * p5 + 90 * p6⟩

/-- A lower bound for `2^(3m) * (a + b r + c r^2 + d r^3)` when `lo / 2^m ≤ r ≤ hi / 2^m`, `0 ≤ lo`. -/
def lowerNum (lo hi : Int) (m : Nat) (x : Z4) : Int :=
  let e : Int := 2 ^ m
  x.a * e * e * e
    + (if 0 ≤ x.b then x.b * lo else x.b * hi) * e * e
    + (if 0 ≤ x.c then x.c * lo * lo else x.c * hi * hi) * e
    + (if 0 ≤ x.d then x.d * lo * lo * lo else x.d * hi * hi * hi)

/-- Certified nonnegativity of `x` at the root `r ∈ [lo / 2^m, hi / 2^m]`. -/
def nonneg (lo hi : Int) (m : Nat) (x : Z4) : Bool := decide (0 ≤ lowerNum lo hi m x)

end Z4

/-- `x * n` has integer coefficients: returns them. -/
def K.toZ4 (n : Int) (x : K) : Z4 :=
  ⟨(x.a * n).num, (x.b * n).num, (x.c * n).num, (x.d * n).num⟩

def K.integralAt (n : Int) (x : K) : Bool :=
  (x.a * n).den == 1 && (x.b * n).den == 1 && (x.c * n).den == 1 && (x.d * n).den == 1

/-- The polynomial `f(x) = x^4 - 4x^3 - 3x^2 - 2x + 2` at `p / 2^m`, times `2^(4m)`. -/
def fNum (p : Int) (m : Nat) : Int :=
  let e : Int := 2 ^ m
  p * p * p * p - 4 * p * p * p * e - 3 * p * p * e * e - 2 * p * e * e * e + 2 * e * e * e * e

/-- `lo / 2^m < r < hi / 2^m` is certified by `f(lo/2^m) > 0 > f(hi/2^m)` with `0 ≤ lo`, `hi ≤ 2^m`
(`f` is decreasing on `[0, 1]`). -/
def enclosureOk (lo hi : Int) (m : Nat) : Bool :=
  decide (0 ≤ lo) && decide (lo < hi) && decide (hi ≤ 2 ^ m) && decide (0 < fNum lo m) &&
    decide (fNum hi m < 0)

end Fast
