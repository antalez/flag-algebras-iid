import BeatAvg.Cert.ThrInv

/-!
# The objective term on arrangements
-/

open MeasureTheory Set Function

namespace BeatAvg

theorem objT_comp (ω : Fin 8 → ℝ) (ρ : Fin 8 → Fin 8) : objT (ω ∘ ρ) = ind S4 ((ω ∘ ρ) ∘ bA) := by
  unfold objT; rw [split_e44]

theorem objT_eval (ω : Fin 8 → ℝ) {ρ : Fin 8 → Fin 8} (hρ : Injective ρ) :
    objT (ω ∘ ρ) = if Fast.succA (cfgOf ω) ρ then 1 else 0 := by
  rw [objT_comp]
  exact ind_eq_ite_bool (succA_iff ω hρ).symm

/-- Agreement up to a permutation of the three summands (positions `0..2`), same target. -/
def RelObj (ρ ρ' : Fin 8 → Fin 8) : Prop :=
  ρ (bA 3) = ρ' (bA 3) ∧
    ∃ b : Equiv.Perm (Fin 3), ∀ i : Fin 3, ρ (bA i.castSucc) = ρ' (bA (b i).castSucc)

instance (ρ ρ' : Fin 8 → Fin 8) : Decidable (RelObj ρ ρ') := by unfold RelObj; infer_instance

theorem objT_congr (ω : Fin 8 → ℝ) {ρ ρ' : Fin 8 → Fin 8} (h : RelObj ρ ρ') :
    objT (ω ∘ ρ) = objT (ω ∘ ρ') := by
  obtain ⟨h3, b, hb⟩ := h
  rw [objT_comp, objT_comp]
  have hS : (ω ∘ ρ) ∘ bA ∈ S4 ↔ (ω ∘ ρ') ∘ bA ∈ S4 :=
    S4_congr (by simp only [comp_apply]; rw [h3]) b
      (fun i => by simp only [comp_apply]; rw [hb])
  by_cases hp : (ω ∘ ρ) ∘ bA ∈ S4
  · rw [ind_of_mem hp, ind_of_mem (hS.1 hp)]
  · rw [ind_of_notMem hp, ind_of_notMem (fun hq => hp (hS.2 hq))]

end BeatAvg
