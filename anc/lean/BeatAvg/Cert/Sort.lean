import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
# Sorting a tuple of reals, measurably
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- The sorted version of a tuple. -/
noncomputable def sortT {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := v ∘ Tuple.sort v

theorem sortT_monotone {n : ℕ} (v : Fin n → ℝ) : Monotone (sortT v) := Tuple.monotone_sort v

theorem sortT_comp_perm {n : ℕ} (v : Fin n → ℝ) (g : Equiv.Perm (Fin n)) :
    sortT (v ∘ g) = sortT v := Tuple.comp_perm_comp_sort_eq_comp_sort

theorem sortT_of_monotone {n : ℕ} {v : Fin n → ℝ} (h : Monotone v) : sortT v = v := by
  unfold sortT
  rw [Tuple.sort_eq_refl_iff_monotone.2 h]
  rfl

theorem measurableSet_sort_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {v : Fin n → ℝ | Tuple.sort v = σ} := by
  have h : {v : Fin n → ℝ | Tuple.sort v = σ} =
      (⋂ i, ⋂ j, {v : Fin n → ℝ | i ≤ j → v (σ i) ≤ v (σ j)}) ∩
      ⋂ i, ⋂ j, {v : Fin n → ℝ | i < j → v (σ i) = v (σ j) → σ i < σ j} := by
    ext v
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i j hij => h1 hij, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i j hij => h1 i j hij, h2⟩
  rw [h]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i ≤ j
    · simp only [hij, forall_true_left]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp [hij]
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, forall_true_left, imp_false]
        have hm : MeasurableSet {v : Fin n → ℝ | v (σ i) = v (σ j)} :=
          measurableSet_eq_fun (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
        exact hm.compl
    · simp [hij]

theorem measurable_sortT {n : ℕ} : Measurable (sortT : (Fin n → ℝ) → Fin n → ℝ) := by
  classical
  refine Measurable.of_eval fun k => ?_
  have h : (fun v : Fin n → ℝ => sortT v k) = fun v =>
      ∑ σ : Equiv.Perm (Fin n), ({v | Tuple.sort v = σ} : Set (Fin n → ℝ)).indicator
        (fun v => v (σ k)) v := by
    funext v
    rw [Finset.sum_eq_single (Tuple.sort v)]
    · simp [sortT]
    · intro σ _ hσ
      simp [Ne.symm hσ]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h]
  exact Finset.measurable_sum _ fun σ _ =>
    (measurable_pi_apply _).indicator (measurableSet_sort_eq σ)

end BeatAvg
