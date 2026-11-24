import Fast.Cert8

/-!
# Positive semidefiniteness of `Y` (computable part)

`Y` is symmetric and `Y = G^T G / 4^gT + R` with `R` diagonally dominant by rows:
`R_aa ≥ ∑_{b ≠ a} |R_ab|`, checked with rational bounds from the enclosure of `r`.
The checks are stated row by row, so that the kernel can evaluate them in pieces.
-/

namespace Fast

/-- Lower bound of `x` at `r ∈ [l, h]`, `0 ≤ l`. -/
def K.lowerQ (l h : Rat) (x : K) : Rat :=
  x.a + (if 0 ≤ x.b then x.b * l else x.b * h) + (if 0 ≤ x.c then x.c * (l * l) else x.c * (h * h))
    + (if 0 ≤ x.d then x.d * (l * l * l) else x.d * (h * h * h))

/-- Upper bound of `x` at `r ∈ [l, h]`, `0 ≤ l`. -/
def K.upperQ (l h : Rat) (x : K) : Rat :=
  x.a + (if 0 ≤ x.b then x.b * h else x.b * l) + (if 0 ≤ x.c then x.c * (h * h) else x.c * (l * l))
    + (if 0 ≤ x.d then x.d * (h * h * h) else x.d * (l * l * l))

/-- Upper bound of `|x|`. -/
def K.absUp (l h : Rat) (x : K) : Rat := max (-(K.lowerQ l h x)) (K.upperQ l h x)

def K.eqb (x y : K) : Bool :=
  decide (x.a = y.a) && decide (x.b = y.b) && decide (x.c = y.c) && decide (x.d = y.d)

def dotL : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- `(G^T G)_{ab}`. -/
def gtg (c : Cert8) (a b : Nat) : Int := dotL (c.Gc.getD a []) (c.Gc.getD b [])

/-- `y - g / 4^gT`. -/
def Rof (c : Cert8) (y : K) (g : Int) : K := y.sub (K.ofRat ((g : Rat) / (4 : Rat) ^ c.gT))

/-- `R = Y - G^T G / 4^gT`. -/
def Rk (c : Cert8) (a b : Nat) : K := Rof c (yAt c.Yr a b) (gtg c a b)

def encL (c : Cert8) : Rat := (c.encLo : Rat) / (2 : Rat) ^ c.encM
def encH (c : Cert8) : Rat := (c.encHi : Rat) / (2 : Rat) ^ c.encM

/-- Sum of the bounds of `|x|` over a row, except at position `a`; the row starts at position `b`. -/
def offSum (l h : Rat) (a : Nat) : Nat → List K → Rat
  | _, [] => 0
  | b, x :: xs => (if b = a then 0 else K.absUp l h x) + offSum l h a (b + 1) xs

/-- Row `a` of `R`, given row `a` of `Y` and column `a` of `G`, is diagonally dominant. -/
def rowOk (c : Cert8) (a : Nat) (yrow : List K) (ca : List Int) : Bool :=
  decide (offSum (encL c) (encH c) a 0 (List.zipWith (fun y cb => Rof c y (dotL ca cb)) yrow c.Gc)
    ≤ K.lowerQ (encL c) (encH c) (Rof c (yrow.getD a K.zero) (dotL ca ca)))

def rowOkI (c : Cert8) (a : Nat) : Bool := rowOk c a (c.Yr.getD a []) (c.Gc.getD a [])

/-- Row `a` of `Y` equals column `a`, right of the diagonal. -/
def symRow (c : Cert8) (a : Nat) : Bool :=
  (List.range 255).all fun b => decide (b ≤ a) || K.eqb (yAt c.Yr a b) (yAt c.Yr b a)

def shapeOk (c : Cert8) : Bool :=
  c.Yr.length == 255 && c.Gc.length == 255 && c.Yr.all (·.length == 255) &&
    c.Gc.all (·.length == 255)

/-- `Y` is symmetric and `Y - G^T G / 4^gT` is diagonally dominant by rows. -/
def psdOk (c : Cert8) : Bool :=
  shapeOk c && (List.range 255).all (symRow c) && (List.range 255).all (rowOkI c)

/-- The multipliers lie in `[0, B]` (certified). -/
def multOk (c : Cert8) : Bool :=
  let ok := fun (x : K) => decide (0 ≤ K.lowerQ (encL c) (encH c) x) &&
    decide (K.upperQ (encL c) (encH c) x ≤ c.B)
  c.lo.toList.all ok && c.hi.toList.all ok && c.w1.toList.all ok && c.w2.toList.all ok

/-- All column indices of `W` are `< 255`. -/
def wOk (c : Cert8) : Bool := c.W.toList.all fun row => row.all fun e => decide (e.1 < 255)

/-- All checks of the certificate that do not involve patterns. -/
def staticOk (c : Cert8) : Bool :=
  enclosureOk c.encLo c.encHi c.encM && integralOk c && psdOk c && wOk c && multOk c &&
    decide (0 < c.Dn) && decide (0 < c.cbarQ) && decide (0 ≤ c.B)

end Fast
