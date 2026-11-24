import BeatAvg.Cert.MkD

/-!
# Tables, block index maps, and coordinates of the splitting maps
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- Finite tables defining certificate data. -/
structure Tab where
  Fflag : Fast.Cfg 5 → ℕ
  Fcls : Fast.Cfg 5 → ℕ
  Qf : ℕ → ℕ → ℝ
  lo : ℕ → ℝ
  hi : ℕ → ℝ
  w1 : ℕ → ℝ
  w2 : ℕ → ℝ
  clo : ℝ

/-- The certificate data of a table. -/
noncomputable def Tab.D (T : Tab) : CertData 300 (Fin 8) :=
  mkD T.Fflag T.Fcls T.Qf T.lo T.hi T.w1 T.w2 T.clo

/-! Block index maps. -/

def bA : Fin 4 → Fin 8 := Fin.castAdd 4
def bB : Fin 4 → Fin 8 := Fin.natAdd 4
def bR : Fin 2 → Fin 8 := Fin.castAdd 6
def bT : Fin 3 → Fin 8 := fun j => Fin.natAdd 2 (Fin.castAdd 3 j)
def bT' : Fin 3 → Fin 8 := fun j => Fin.natAdd 2 (Fin.natAdd 3 j)
def bZ : Fin 1 → Fin 8 := Fin.castAdd 7
def bS : Fin 4 → Fin 8 := fun j => Fin.natAdd 1 (Fin.castAdd 3 j)
def bW : Fin 3 → Fin 8 := fun j => Fin.natAdd 1 (Fin.natAdd 4 j)

theorem split_e44 (v : Fin 8 → ℝ) : split e44 v = (v ∘ bA, v ∘ bB) := by
  simp only [split, e44, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rfl

theorem split3_e233 (v : Fin 8 → ℝ) : split3 e233 v = (v ∘ bR, (v ∘ bT, v ∘ bT')) := by
  simp only [split3, e233, Sum.map_inl, Sum.map_inr, id, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  rfl

theorem split3_e143 (v : Fin 8 → ℝ) : split3 e143 v = (v ∘ bZ, (v ∘ bS, v ∘ bW)) := by
  simp only [split3, e143, Sum.map_inl, Sum.map_inr, id, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  rfl

theorem bA_val (i : Fin 4) : (bA i).val = i.val := rfl
theorem bB_val (i : Fin 4) : (bB i).val = 4 + i.val := rfl
theorem bR_val (i : Fin 2) : (bR i).val = i.val := rfl
theorem bT_val (i : Fin 3) : (bT i).val = 2 + i.val := rfl
theorem bT'_val (i : Fin 3) : (bT' i).val = 2 + (3 + i.val) := rfl
theorem bZ_val (i : Fin 1) : (bZ i).val = i.val := rfl
theorem bS_val (i : Fin 4) : (bS i).val = 1 + i.val := rfl
theorem bW_val (i : Fin 3) : (bW i).val = 1 + (4 + i.val) := rfl

end BeatAvg
