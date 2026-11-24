import BeatAvg.Cert.FlagBound
import BeatAvg.Four.Config

namespace BeatAvg.Four
open MeasureTheory Function

/-- Ordinary general position, additionally avoiding the three ratio boundaries. -/
def Generic {n : ℕ} (v : Fin n → ℝ) : Prop :=
  GenericN n v ∧ ∀ q : Fin 3, ∀ i j : Fin n, i ≠ j → v i ≠ cut q * v j

theorem ae_generic {n : ℕ} {μ : Measure ℝ} (hμ : IsLaw μ) [NullSingletonClass μ] :
    ∀ᵐ v ∂(iid n μ), Generic v := by
  have := hμ.prob
  have hc : ∀ᵐ v ∂(iid n μ),
      ∀ q : Fin 3, ∀ i j : Fin n, i ≠ j → v i ≠ cut q * v j := by
    simp only [ae_all_iff]
    intro q i j hij
    have h := pi_graph_null (ι := Fin n) μ i (fun v => cut q * v j) (by fun_prop)
      (fun v y => by simp [Function.update_of_ne (Ne.symm hij)])
    rw [ae_iff]
    simpa using h
  filter_upwards [ae_genericN hμ, hc] with v hv hvc
  exact ⟨hv, hvc⟩

theorem Generic.comp_perm {n : ℕ} {v : Fin n → ℝ} (hv : Generic v)
    (σ : Equiv.Perm (Fin n)) : Generic (v ∘ σ) := by
  refine ⟨⟨fun i => hv.1.1 _, hv.1.2.1.comp σ.injective, ?_⟩, ?_⟩
  · intro a b c d had hbd hcd
    exact hv.1.2.2 _ _ _ _ (σ.injective.ne had) (σ.injective.ne hbd) (σ.injective.ne hcd)
  · intro q i j hij
    exact hv.2 q _ _ (σ.injective.ne hij)

end BeatAvg.Four
