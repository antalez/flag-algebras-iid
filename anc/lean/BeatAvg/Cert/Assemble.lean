import BeatAvg.Cert.Invariance

/-!
# The functional of a sorted sample as a sum over canonical arrangements
-/

open MeasureTheory Set Function

namespace BeatAvg

theorem lam_split (T : Tab) (x : ℝ) (v : Fin 8 → ℝ) :
    lam T.D x v = objT v + sqPart T v + degPart T x v + thrPart T x v := by
  simp only [lam, sqPart, degPart, thrPart]
  ring

/-- The value of `8! * Λ` on a sorted sample with configuration `c`. -/
noncomputable def LamR (T : Tab) (c : Fast.Cfg 8) (x : ℝ) : ℝ :=
  144 * (Fast.repsObj.map fun l => if Fast.succA c (Fast.fnOf l) then (1 : ℝ) else 0).sum
    + 72 * (Fast.repsSq.map fun l => sqR T c (Fast.fnOf l)).sum
    + 48 * (Fast.repsDeg.map fun l => degR T c (Fast.fnOf l) x).sum
    + 144 * (Fast.repsThr.map fun l => thrR T c (Fast.fnOf l) x).sum

theorem sum_obj (ω : Fin 8 → ℝ) :
    ∑ π : Equiv.Perm (Fin 8), objT (ω ∘ ⇑π)
      = 144 * (Fast.repsObj.map fun l => if Fast.succA (cfgOf ω) (Fast.fnOf l) then (1 : ℝ) else 0).sum := by
  have h := sum_of_facts embA3 embB emb0 (by decide) (by decide) (by decide)
    (fun ρ => objT (ω ∘ ρ)) (obj_inv1 ω) (obj_inv2 ω) (obj_inv3 ω) obj_facts (by decide)
  have hK : ((Nat.factorial 3 * Nat.factorial 4 * Nat.factorial 0 : ℕ) : ℝ) = 144 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 2
  exact List.map_congr_left fun l hl => objT_eval ω (obj_facts.good l hl).2.1

theorem sum_sq (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) :
    ∑ π : Equiv.Perm (Fin 8), sqPart T (ω ∘ ⇑π)
      = 72 * (Fast.repsSq.map fun l => sqR T (cfgOf ω) (Fast.fnOf l)).sum := by
  have h := sum_of_facts embR embT embT' (by decide) (by decide) (by decide)
    (fun ρ => sqPart T (ω ∘ ρ)) (sq_inv1 T ω) (sq_inv2 T ω) (sq_inv3 T ω) sq_facts (by decide)
  have hK : ((Nat.factorial 2 * Nat.factorial 3 * Nat.factorial 3 : ℕ) : ℝ) = 72 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨-, hi, g1, g2, g3⟩ := sq_facts.good l hl
  exact sqPart_eval T hω hi (mono_of_lt g1) (mono_of_lt g2) (mono_of_lt g3)

theorem sum_deg (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) (x : ℝ) :
    ∑ π : Equiv.Perm (Fin 8), degPart T x (ω ∘ ⇑π)
      = 48 * (Fast.repsDeg.map fun l => degR T (cfgOf ω) (Fast.fnOf l) x).sum := by
  have h := sum_of_facts embS embW2 emb0 (by decide) (by decide) (by decide)
    (fun ρ => degPart T x (ω ∘ ρ)) (deg_inv1 T ω x) (deg_inv2 T ω x) (deg_inv3 T ω x) deg_facts
    (by decide)
  have hK : ((Nat.factorial 4 * Nat.factorial 2 * Nat.factorial 0 : ℕ) : ℝ) = 48 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨-, hi, g1, -, -⟩ := deg_facts.good l hl
  exact degPart_eval T hω hi (mono_of_lt g1) x

theorem sum_thr (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) (x : ℝ) :
    ∑ π : Equiv.Perm (Fin 8), thrPart T x (ω ∘ ⇑π)
      = 144 * (Fast.repsThr.map fun l => thrR T (cfgOf ω) (Fast.fnOf l) x).sum := by
  have h := sum_of_facts embA embB3 emb0 (by decide) (by decide) (by decide)
    (fun ρ => thrPart T x (ω ∘ ρ)) (thr_inv1 T ω x) (thr_inv2 T ω x) (thr_inv3 T ω x) thr_facts
    (by decide)
  have hK : ((Nat.factorial 4 * Nat.factorial 3 * Nat.factorial 0 : ℕ) : ℝ) = 144 := by
    norm_num [Nat.factorial]
  rw [h, hK]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨-, hi, g1, -, -⟩ := thr_facts.good l hl
  exact thrPart_eval T hω hi (mono_of_lt g1) x

/-- On a sorted sample in general position, `8! Λ(x)` is a function of the configuration. -/
theorem Lam_sorted (T : Tab) {ω : Fin 8 → ℝ} (hω : SG8 ω) (x : ℝ) :
    Lam T.D x ω = (1 / (Nat.factorial 8 : ℝ)) * LamR T (cfgOf ω) x := by
  unfold Lam LamR
  congr 1
  simp only [lam_split, Finset.sum_add_distrib]
  rw [sum_obj ω, sum_sq T hω, sum_deg T hω x, sum_thr T hω x]

end BeatAvg
