import Fast.Pat

/-!
# Generic versions used at order 7 (computable part)
-/

namespace Fast

/-- Concatenation of two tuples. -/
@[inline] def appendF {α : Type} {t m : Nat} (u : Fin t → α) (v : Fin m → α) : Fin (t + m) → α :=
  fun i => if h : i.val < t then u ⟨i.val, h⟩ else v ⟨i.val - t, by omega⟩

/-- Sum bit of a sorted sample with pattern `P`, with a given index function for quadruples. -/
def sbPatG (idx : Nat → Nat → Nat → Nat → Nat) (P : Array Nat) (a b c d : Nat) : Bool :=
  let x := min a (min b c)
  let z := max a (max b c)
  let y := a + b + c - x - z
  if x < y ∧ y < z then
    if z < d then decide (1 ≤ P[idx x y z d]!)
    else if y < d ∧ d < z then decide (P[idx x y d z]! = 2)
    else false
  else false

/-- The configuration of a sorted sample of `n` points with pattern `P`. -/
def cfgOfPatG (n : Nat) (idx : Nat → Nat → Nat → Nat → Nat) (P : Array Nat) : Cfg n :=
  ⟨fun i j => decide (i.val < j.val), fun a b c d => sbPatG idx P a.val b.val c.val d.val⟩

/-- Index table for `n = 7`. -/
def idx7Tab : Array Nat := Array.ofFn (idxFn 7)

@[inline] def idx7 (a b c d : Nat) : Nat := idx7Tab[a * 512 + b * 64 + c * 8 + d]!

end Fast
