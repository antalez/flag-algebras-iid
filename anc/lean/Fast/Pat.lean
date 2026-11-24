/-!
# Patterns of sorted samples (computable part)

A pattern of `n` points is an array of trits indexed by the 4-subsets `a < b < c < d < n`
in lexicographic order.
-/

namespace Fast

/-- The 4-subsets of `{0..n-1}` as increasing quadruples, in lexicographic order. -/
def combos (n : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b => (List.range n).flatMap fun c =>
    (List.range n).filterMap fun d => if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

/-- Position of a quadruple in `combos n` (linear search; used to build tables only). -/
def comboIdx (n : Nat) (q : Nat × Nat × Nat × Nat) : Nat := (combos n).idxOf q

/-- Entry `k = 512 a + 64 b + 8 c + d` of the index table for `n` points. -/
def idxFn (n : Nat) (k : Fin 4096) : Nat :=
  comboIdx n (k.val / 512, (k.val / 64) % 8, (k.val / 8) % 8, k.val % 8)

/-- Index tables for `n = 8`: `idx8 a b c d` for `a < b < c < d < 8`. -/
def idx8Tab : Array Nat := Array.ofFn (idxFn 8)

@[inline] def idx8 (a b c d : Nat) : Nat := idx8Tab[a * 512 + b * 64 + c * 8 + d]!

/-- Deleting the point `d`: the increasing injection skipping `d`. -/
@[inline] def skip (d i : Nat) : Nat := if i < d then i else i + 1

/-- A configuration of `n` points: order bits and sum bits
(`sb a b c d` stands for `v a + v b + v c < 2 v d`, for distinct indices). -/
structure Cfg (n : Nat) where
  lt : Fin n → Fin n → Bool
  sb : Fin n → Fin n → Fin n → Fin n → Bool

def Cfg.comap {m n : Nat} (c : Cfg n) (ι : Fin m → Fin n) : Cfg m :=
  ⟨fun i j => c.lt (ι i) (ι j), fun a b e d => c.sb (ι a) (ι b) (ι e) (ι d)⟩

/-- Sum bit of a sorted sample with pattern `P` (8 points). For distinct `a, b, c, d`:
the target `d` succeeds iff it is the largest and the trit is at least 1, or it is the second
largest and the trit is 2. -/
def sbPat (P : Array Nat) (a b c d : Nat) : Bool :=
  -- sort a, b, c
  let x := min a (min b c)
  let z := max a (max b c)
  let y := a + b + c - x - z
  if x < y ∧ y < z then
    if z < d then decide (1 ≤ P[idx8 x y z d]!)
    else if y < d ∧ d < z then decide (P[idx8 x y d z]! = 2)
    else false
  else false

/-- The configuration of a sorted sample with pattern `P`. -/
def cfgOfPat (P : Array Nat) : Cfg 8 :=
  ⟨fun i j => decide (i.val < j.val), fun a b c d => sbPat P a.val b.val c.val d.val⟩

end Fast

namespace Fast

/-- Root triples of the thresholds: `θ % 4 = 0, 1, 2, 3` ↦ `(0,1,2), (0,1,3), (0,2,3), (1,2,3)`. -/
def tripI (t : Nat) : Fin 4 := if t % 4 = 3 then 1 else 0
def tripJ (t : Nat) : Fin 4 := if t % 4 = 0 ∨ t % 4 = 1 then 1 else 2
def tripK (t : Nat) : Fin 4 := if t % 4 = 0 then 2 else 3

end Fast
