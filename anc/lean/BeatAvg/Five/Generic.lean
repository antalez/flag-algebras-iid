import BeatAvg.Bounded

open MeasureTheory Set Function
namespace BeatAvg.Five

/-- General position for colored sample points: nonnegative, distinct, no ties. -/
def Generic {n : ℕ} (ω : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ ω i) ∧ Function.Injective ω ∧
    (∀ a b c d : Fin n, a ≠ d → b ≠ d → c ≠ d → ω a + ω b + ω c ≠ 2 * ω d) ∧
    ∀ i j : Fin n, i ≠ j → ω i ≠ 2 * ω j

/-- Lemma 1.2: a sample from an atomless law is almost surely in general position. -/
theorem ae_generic {n : ℕ} {μ : Measure ℝ} (hμ : IsLaw μ) [NullSingletonClass μ] :
    ∀ᵐ ω ∂(iid n μ), Generic ω := by
  have := hμ.prob
  have h1 := iid_nonneg_ae (n := n) hμ
  have h2 : ∀ᵐ ω ∂(iid n μ), ∀ i j : Fin n, i ≠ j → ω i ≠ ω j := by
    simp only [ae_all_iff]
    intro i j hij
    have h := pi_graph_null (ι := Fin n) μ i (fun ω => ω j) (measurable_pi_apply j)
      (fun ω y => by simp [Function.update_of_ne (Ne.symm hij)])
    rw [ae_iff]
    simpa using h
  have h3 : ∀ᵐ ω ∂(iid n μ), ∀ a b c d : Fin n, a ≠ d → b ≠ d → c ≠ d →
      ω a + ω b + ω c ≠ 2 * ω d := by
    simp only [ae_all_iff]
    intro a b c d had hbd hcd
    have h := pi_graph_null (ι := Fin n) μ d (fun ω => (ω a + ω b + ω c) / 2) (by fun_prop)
      (fun ω y => by simp [Function.update_of_ne had, Function.update_of_ne hbd,
        Function.update_of_ne hcd])
    rw [ae_iff]
    refine measure_mono_null ?_ h
    intro ω hω
    simp only [mem_ofPred_eq, not_not] at hω ⊢
    linarith
  have h4 : ∀ᵐ ω ∂(iid n μ), ∀ i j : Fin n, i ≠ j → ω i ≠ 2 * ω j := by
    simp only [ae_all_iff]
    intro i j hij
    have h := pi_graph_null (ι := Fin n) μ i (fun ω => 2 * ω j) (by fun_prop)
      (fun ω y => by simp [Function.update_of_ne (Ne.symm hij)])
    rw [ae_iff]
    simpa using h
  filter_upwards [h1, h2, h3, h4] with ω g1 g2 g3 g4
  refine ⟨g1, (fun i j hij => ?_), g3, g4⟩
  by_contra hne
  exact g2 i j hne hij

end BeatAvg.Five
