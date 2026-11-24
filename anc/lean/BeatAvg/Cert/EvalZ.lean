import BeatAvg.Cert.Assemble
import BeatAvg.Cert.KSign
import Fast.Tables

/-!
# The integer evaluation computes the functional
-/

open Function

namespace BeatAvg

/-- The real tables of integer tables. -/
noncomputable def tabOf (t : Fast.Tabs) : Tab where
  Fflag := Fast.Fflag t.ft
  Fcls := Fast.Fcls t.ct
  Qf i j := evalZ (t.QZ[i * 300 + j]!) / t.Dn
  lo c := evalZ (t.loZ[c]!) / t.Dn
  hi c := evalZ (t.hiZ[c]!) / t.Dn
  w1 θ := evalZ (t.w1Z[θ]!) / t.Dn
  w2 θ := evalZ (t.w2Z[θ]!) / t.Dn
  clo := Bstar

theorem evalZ_foldl (l : List Fast.Z4) (acc : Fast.Z4) :
    evalZ (l.foldl Fast.Z4.add acc) = evalZ acc + (l.map evalZ).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, evalZ_add, List.map_cons, List.sum_cons]; ring

theorem evalZ_zsum (l : List Fast.Z4) : evalZ (Fast.zsum l) = (l.map evalZ).sum := by
  unfold Fast.zsum
  rw [evalZ_foldl, evalZ_zero, zero_add]

theorem evalZ_ofInt (n : ℤ) : evalZ (Fast.Z4.ofInt n) = n := by
  simp [evalZ, Fast.Z4.ofInt]

theorem evalZ_b4 : evalZ Fast.b4 = 4 * Bstar := by
  simp only [evalZ, Fast.b4, Bstar]; push_cast; ring

theorem sum_map_ite_countP {α : Type*} (l : List α) (p : α → Bool) :
    (l.map fun a => if p a then (1 : ℝ) else 0).sum = (l.countP p : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h]; ring

variable (t : Fast.Tabs) (c : Fast.Cfg 8) (ρ : Fin 8 → Fin 8)

theorem sqZ_eval (hDn : (t.Dn : ℝ) ≠ 0) :
    evalZ (Fast.sqZ t c ρ) = t.Dn * sqR (tabOf t) c ρ := by
  unfold Fast.sqZ sqR
  simp only [tabOf]
  rw [mul_div_cancel₀ _ hDn]

theorem deg_eval (hDn : (t.Dn : ℝ) ≠ 0) (x : ℝ) :
    evalZ (Fast.degU t c ρ) + 4 * x * evalZ (Fast.degV t c ρ)
      = 4 * t.Dn * degR (tabOf t) c ρ x := by
  unfold Fast.degU Fast.degV degR
  simp only [tabOf, evalZ_sub, evalZ_mul, evalZ_smul, evalZ_ofInt, evalZ_b4]
  push_cast
  field_simp
  ring

theorem thrUθ_eval (θ : Fin 8) :
    evalZ (Fast.thrUθ t c ρ θ) = evalZ (t.w1Z[θ.val]!) *
        (-4 * (if Fast.succF c ρ && Fast.allBelow c ρ θ.val then 1 else 0))
      + evalZ (t.w2Z[θ.val]!) * (4 * (if Fast.succF c ρ && Fast.below c ρ θ.val 7 then 1 else 0)
        - 4 * Bstar * (if Fast.allBelow c ρ θ.val then 1 else 0)) := by
  unfold Fast.thrUθ
  simp only [evalZ_add, evalZ_smul, evalZ_mul, evalZ_sub, evalZ_ofInt]
  by_cases h1 : (Fast.succF c ρ && Fast.allBelow c ρ θ.val) = true <;>
    by_cases h2 : (Fast.succF c ρ && Fast.below c ρ θ.val 7) = true <;>
    by_cases h3 : Fast.allBelow c ρ θ.val = true <;>
    simp [h1, h2, h3, evalZ_b4] <;> ring

end BeatAvg

namespace BeatAvg

variable (t : Fast.Tabs) (c : Fast.Cfg 8) (ρ : Fin 8 → Fin 8)

theorem thr_eval (hDn : (t.Dn : ℝ) ≠ 0) (x : ℝ) :
    evalZ (Fast.thrU t c ρ) + 4 * x * evalZ (Fast.thrV t c ρ)
      = 4 * t.Dn * thrR (tabOf t) c ρ x := by
  unfold Fast.thrU Fast.thrV thrR
  by_cases h : Fast.ty0 c ρ = true
  · simp only [h, if_true]
    rw [evalZ_zsum, evalZ_zsum, List.map_map, List.map_map, Finset.mul_sum, Fin.sum_univ_def,
      ← List.sum_map_mul_left, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun θ _ => ?_
    simp only [comp_apply, thrUθ_eval, tabOf]
    by_cases h3 : Fast.allBelow c ρ θ.val = true
    · simp only [h3, if_true]
      field_simp
      ring
    · simp only [h3, if_false, Bool.false_eq_true, evalZ_zero]
      field_simp
      ring
  · simp only [h, if_false, Bool.false_eq_true, evalZ_zero]
    ring

/-- The integer evaluation: `4 · Dn · LamR(x) = U + 4x · V`. -/
theorem lamUV_eval (hDn : (t.Dn : ℝ) ≠ 0) (x : ℝ) :
    evalZ (Fast.lamU t c) + 4 * x * evalZ (Fast.lamV t c) = 4 * t.Dn * LamR (tabOf t) c x := by
  have hsq : ((Fast.repsSq.map fun l => Fast.sqZ t c (Fast.fnOf l)).map evalZ).sum
      = t.Dn * (Fast.repsSq.map fun l => sqR (tabOf t) c (Fast.fnOf l)).sum := by
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun l _ => sqZ_eval t c _ hDn
  have hdeg : ((Fast.repsDeg.map fun l => Fast.degU t c (Fast.fnOf l)).map evalZ).sum
      + 4 * x * ((Fast.repsDeg.map fun l => Fast.degV t c (Fast.fnOf l)).map evalZ).sum
      = 4 * t.Dn * (Fast.repsDeg.map fun l => degR (tabOf t) c (Fast.fnOf l) x).sum := by
    rw [List.map_map, List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun l _ => deg_eval t c _ hDn x
  have hthr : ((Fast.repsThr.map fun l => Fast.thrU t c (Fast.fnOf l)).map evalZ).sum
      + 4 * x * ((Fast.repsThr.map fun l => Fast.thrV t c (Fast.fnOf l)).map evalZ).sum
      = 4 * t.Dn * (Fast.repsThr.map fun l => thrR (tabOf t) c (Fast.fnOf l) x).sum := by
    rw [List.map_map, List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun l _ => thr_eval t c _ hDn x
  have hobj : (Fast.repsObj.map fun l => if Fast.succA c (Fast.fnOf l) then (1 : ℝ) else 0).sum
      = (Fast.cntObj c : ℝ) := by
    unfold Fast.cntObj
    exact sum_map_ite_countP Fast.repsObj fun l => Fast.succA c (Fast.fnOf l)
  unfold Fast.lamU Fast.lamV LamR
  simp only [evalZ_add, evalZ_smul, evalZ_ofInt, evalZ_zsum]
  rw [hobj]
  push_cast
  linear_combination 288 * hsq + 48 * hdeg + 144 * hthr

end BeatAvg
