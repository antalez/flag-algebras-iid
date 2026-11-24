import Fast.K
import Fast.Eval
import Fast.Canon

/-!
# Integer tables and the evaluation of `4 · Dn · 8! · Λ(x) = U + 4x · V` (computable part)
-/

namespace Fast

/-- Index of the pair of ranks `p < q` among the ten pairs. -/
@[inline] def pairIdx (p q : Nat) : Nat := p * (9 - p) / 2 + (q - p - 1)

@[inline] def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Trit of the quadruple of points `a, b, e, d` (in increasing order of rank). -/
@[inline] def trit5 (c : Cfg 5) (a b e d : Fin 5) : Nat := b2n (c.sb a b e d) + b2n (c.sb a b d e)

/-- Code of the pattern of five points listed in increasing order of rank:
trits of the quadruples in lexicographic order. -/
@[inline] def code5 (c : Cfg 5) (i0 i1 i2 i3 i4 : Fin 5) : Nat :=
  trit5 c i0 i1 i2 i3 + 3 * trit5 c i0 i1 i2 i4 + 9 * trit5 c i0 i1 i3 i4 + 27 * trit5 c i0 i2 i3 i4
    + 81 * trit5 c i1 i2 i3 i4

/-- Flag of five points. Positions 0, 1 are the roots, in increasing order; positions 2, 3, 4 are
the other three points, in increasing order. -/
def Fflag (ft : Array Nat) (c : Cfg 5) : Nat :=
  -- rank of the first root: number of other points below it; rank of the second: one more
  let p := b2n (c.lt 2 0) + b2n (c.lt 3 0) + b2n (c.lt 4 0)
  let q := b2n (c.lt 2 1) + b2n (c.lt 3 1) + b2n (c.lt 4 1) + 1
  -- the point of rank k: a root if k = p or k = q, otherwise the next of the other three points
  let inv : Nat → Fin 5 := fun k =>
    if k = p then 0 else if k = q then 1
    else Fin.ofNat 5 (2 + k - b2n (decide (p < k)) - b2n (decide (q < k)))
  ft[code5 c (inv 0) (inv 1) (inv 2) (inv 3) (inv 4) * 10 + pairIdx p q]!

/-- Class of five points. Position 0 is the root; positions 1..4 are the other points, in
increasing order. -/
def Fcls (ct : Array Nat) (c : Cfg 5) : Nat :=
  let p := b2n (c.lt 1 0) + b2n (c.lt 2 0) + b2n (c.lt 3 0) + b2n (c.lt 4 0)
  let inv : Nat → Fin 5 := fun k =>
    if k = p then 0 else Fin.ofNat 5 (1 + k - b2n (decide (p < k)))
  ct[code5 c (inv 0) (inv 1) (inv 2) (inv 3) (inv 4) * 5 + p]!

/-- Integer tables: flags, classes, and the certificate numbers multiplied by `Dn`. -/
structure Tabs where
  ft : Array Nat
  ct : Array Nat
  QZ : Array Z4
  loZ : Array Z4
  hiZ : Array Z4
  w1Z : Array Z4
  w2Z : Array Z4
  Dn : Int

/-- `4 B* = 6 r - 6 r^2 + r^3`. -/
def b4 : Z4 := ⟨0, 6, -6, 1⟩

def Z4.ofInt (n : Int) : Z4 := ⟨n, 0, 0, 0⟩

def zsum (l : List Z4) : Z4 := l.foldl Z4.add Z4.zero

def sqZ (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Z4 :=
  t.QZ[(Fflag t.ft (c.comap (ρ ∘ first5)) % 300) * 300 + Fflag t.ft (c.comap (ρ ∘ sel2)) % 300]!

def degU (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Z4 :=
  let cls := Fcls t.ct (c.comap (ρ ∘ first5))
  let s : Int := s4C c ρ
  ((t.loZ[cls]!).mul ((Z4.ofInt s).sub b4)).sub (Z4.smul s (t.hiZ[cls]!))

def degV (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Z4 :=
  t.hiZ[Fcls t.ct (c.comap (ρ ∘ first5))]!

def thrUθ (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) (θ : Fin 8) : Z4 :=
  let ab := allBelow c ρ θ.val
  let sf := succF c ρ
  (Z4.smul (if sf && ab then -4 else 0) (t.w1Z[θ.val]!)).add
    ((t.w2Z[θ.val]!).mul ((Z4.ofInt (if sf && below c ρ θ.val 7 then 4 else 0)).sub
      (if ab then b4 else Z4.zero)))

def thrU (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Z4 :=
  if ty0 c ρ then zsum ((List.finRange 8).map (thrUθ t c ρ)) else Z4.zero

def thrV (t : Tabs) (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Z4 :=
  if ty0 c ρ then
    zsum ((List.finRange 8).map fun θ => if allBelow c ρ θ.val then t.w1Z[θ.val]! else Z4.zero)
  else Z4.zero

def cntObj (c : Cfg 8) : Nat := repsObj.countP fun l => succA c (fnOf l)

/-- `4 · Dn · LamR(x) = U + 4x · V`. -/
def lamU (t : Tabs) (c : Cfg 8) : Z4 :=
  (Z4.ofInt (576 * t.Dn * (cntObj c : Int))).add
    ((Z4.smul 288 (zsum (repsSq.map fun l => sqZ t c (fnOf l)))).add
      ((Z4.smul 48 (zsum (repsDeg.map fun l => degU t c (fnOf l)))).add
        (Z4.smul 144 (zsum (repsThr.map fun l => thrU t c (fnOf l))))))

def lamV (t : Tabs) (c : Cfg 8) : Z4 :=
  (Z4.smul 48 (zsum (repsDeg.map fun l => degV t c (fnOf l)))).add
    (Z4.smul 144 (zsum (repsThr.map fun l => thrV t c (fnOf l))))

end Fast

namespace Fast

/-- Certified `Λ(B*) ≤ B*` for the configuration `c`: `8! · Dn · 4B* - U - 4B* · V ≥ 0`. -/
def checkB (lo hi : Int) (m : Nat) (t : Tabs) (c : Cfg 8) : Bool :=
  Z4.nonneg lo hi m (((Z4.smul (40320 * t.Dn) b4).sub (lamU t c)).sub (b4.mul (lamV t c)))

/-- Certified `Λ(p/q) ≤ (p - e)/q` for the configuration `c`:
`4 · Dn · 8! · (p - e) - q · U - 4p · V ≥ 0`. -/
def checkC (lo hi : Int) (m : Nat) (t : Tabs) (p q e : Int) (c : Cfg 8) : Bool :=
  Z4.nonneg lo hi m (((Z4.ofInt (4 * t.Dn * 40320 * (p - e))).sub (Z4.smul q (lamU t c))).sub
    (Z4.smul (4 * p) (lamV t c)))

/-- Both checks, computing `U` and `V` once. -/
def checkBoth (lo hi : Int) (m : Nat) (t : Tabs) (p q e : Int) (c : Cfg 8) : Bool :=
  let U := lamU t c
  let V := lamV t c
  Z4.nonneg lo hi m (((Z4.smul (40320 * t.Dn) b4).sub U).sub (b4.mul V)) &&
    Z4.nonneg lo hi m (((Z4.ofInt (4 * t.Dn * 40320 * (p - e))).sub (Z4.smul q U)).sub
      (Z4.smul (4 * p) V))

end Fast
