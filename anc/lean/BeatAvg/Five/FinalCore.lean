import BeatAvg.Five.Evaluation
import Fast.Five.AssembledCheck

namespace BeatAvg.Five
open Fast.Five Function

/-- The real sample inequalities follow from the checked finite assembly identities. -/
theorem sample_bounds_of_assembly
    (hcheck : ∀ p ∈ Data.patterns.toList, assembledOk p = true)
    (v : Fin 5 → ℝ) (hv : Generic v) :
    Lam Bstar v ≤ Bstar ∧ Lam 1 v ≤ 1-9/10000 := by
  let σ := Tuple.sort v
  have hs : Generic (v ∘ σ) := hv.comp_perm σ
  have hm : Monotone (v ∘ σ) := Tuple.monotone_sort v
  obtain ⟨p, hp, hbits, hb, h1⟩ := sorted_sample_covered hs hm
  have hc := hcheck p hp
  simp only [assembledOk, Bool.and_eq_true] at hc
  have heB := Lam_eval hs hm hbits Fast.K.bstar
  have he1 := Lam_eval hs hm hbits Fast.K.one
  rw [evalK_bstar, keq_sound hc.1] at heB
  rw [show evalK Fast.K.one = 1 by norm_num [evalK, Fast.K.one], keq_sound hc.2] at he1
  rw [Lam_comp_perm] at heB he1
  constructor
  · rw [heB]; exact hb
  · rw [he1]; exact h1

theorem C_le_Bstar_of_assembly
    (hcheck : ∀ p ∈ Data.patterns.toList, assembledOk p = true) : C ≤ Bstar :=
  C_le_Bstar_of_endpoints
    (fun v hv => (sample_bounds_of_assembly hcheck v hv).1)
    (fun v hv => (sample_bounds_of_assembly hcheck v hv).2)

end BeatAvg.Five
