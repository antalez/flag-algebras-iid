import Fast.Pat

/-!
# Evaluation of the terms of the functional from a configuration (computable part)

`c : Cfg 8` is the configuration of the sample and `ρ : Fin 8 → Fin 8` an arrangement of the points.
-/

namespace Fast

/-- Position `i < 4` among the roots, as a position in `Fin 8`. -/
@[inline] def rootPos (i : Fin 4) : Fin 8 := Fin.castAdd 4 i

/-- The point at position `p` lies below the threshold `θ` of the roots at positions `0..3`. -/
def below (c : Cfg 8) (ρ : Fin 8 → Fin 8) (θ : Nat) (p : Fin 8) : Bool :=
  if θ < 4 then
    c.sb (ρ p) (ρ (rootPos (tripI θ))) (ρ (rootPos (tripK θ))) (ρ (rootPos (tripJ θ)))
  else
    c.lt (ρ p) (ρ (rootPos (tripK θ))) ||
      !c.sb (ρ (rootPos (tripI θ))) (ρ (rootPos (tripJ θ))) (ρ (rootPos (tripK θ))) (ρ p)

/-- The roots at positions `0..3` have type 0. -/
def ty0 (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Bool := !c.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)

/-- All fresh points (positions `4..7`) lie below the threshold. -/
def allBelow (c : Cfg 8) (ρ : Fin 8 → Fin 8) (θ : Nat) : Bool :=
  below c ρ θ 4 && below c ρ θ 5 && below c ρ θ 6 && below c ρ θ 7

/-- The fresh points succeed (target at position 7). -/
def succF (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Bool := c.sb (ρ 4) (ρ 5) (ρ 6) (ρ 7)

/-- The first four points succeed (target at position 3). -/
def succA (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Bool := c.sb (ρ 0) (ρ 1) (ρ 2) (ρ 3)

end Fast

namespace Fast

/-- Positions `0, 1, 2, 3, 4`. -/
@[inline] def first5 (i : Fin 5) : Fin 8 := Fin.castAdd 3 i

/-- Positions `0, 1, 5, 6, 7`. -/
@[inline] def sel2 (i : Fin 5) : Fin 8 :=
  if h : i.val < 2 then ⟨i.val, by omega⟩ else ⟨i.val + 3, by omega⟩

/-- Number of successful positions among the root (position 0) and the points at positions 5, 6, 7,
counted as in `s4`: three times "target at position 7" plus "target the root". -/
def s4C (c : Cfg 8) (ρ : Fin 8 → Fin 8) : Nat :=
  (if c.sb (ρ 0) (ρ 5) (ρ 6) (ρ 7) then 3 else 0) + (if c.sb (ρ 5) (ρ 6) (ρ 7) (ρ 0) then 1 else 0)

end Fast
