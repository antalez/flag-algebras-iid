module
public import LeanProofs.Probability
public import LeanProofs.OptimizedLadder
public import LeanProofs.AboveEndpoint
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped Classical
namespace Endpoint

def event (c : ℝ) : Set (Quad ℝ) :=
  {a | a.1 + a.2.1 + a.2.2.1 < c * a.2.2.2}

def probability (μ : PMF ℝ) (c : ℝ) : ℝ :=
  ((draws4 μ).toMeasure (event c)).toReal

theorem Law.probability_eq {α : Type} [Fintype α] (L : Law α) (c : ℝ) :
    probability L.pmf c = L.prob c := by
  unfold probability event
  rw [L.real_event c, ENNReal.toReal_ofReal (L.prob_nonneg c)]

theorem Law.support_finite {α : Type} [Fintype α] (L : Law α) : L.pmf.support.Finite := by
  rw [L.pmf_eq_map_labels, PMF.support_map]
  exact (Set.toFinite _).image _

/-- Actual finite-support probability laws approach the exact algebraic ladder
value. This is a lower bound; no global sharpness claim is made. -/
theorem ladder_probability_lower (e : ℝ) (he : 0 < e) :
    ∃ μ : PMF ℝ, μ.support.Finite ∧ (∀ x ∈ μ.support, 0 ≤ x) ∧
      OptimizedLadder.value - e < probability μ (1 + Real.sqrt 2) := by
  obtain ⟨α, f, L, hL⟩ := OptimizedLadder.probability_witness e he
  let := f
  refine ⟨L.pmf, L.support_finite, L.pmf_nonneg, ?_⟩
  rwa [L.probability_eq]

/-- A decimal lower bound with all displayed digits certified by exact rational
arithmetic. The witness is a genuine law, not just a bound on a formal series. -/
theorem ladder_probability_numerical :
    ∃ μ : PMF ℝ, μ.support.Finite ∧ (∀ x ∈ μ.support, 0 ≤ x) ∧
      (4952063382580596903 / 10000000000000000000 : ℝ) < probability μ (1 + Real.sqrt 2) := by
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup (attainable_nonempty kappa)
    OptimizedLadder.numerical_lower
  rcases hv with ⟨α, f, L, rfl⟩
  let := f
  exact ⟨L.pmf, L.support_finite, L.pmf_nonneg, by rwa [L.probability_eq]⟩

/-- A law with at most five support points works for EVERY strict increase of c
past the endpoint, with a uniform gap of 20/6561 above one half. -/
theorem above_endpoint_probability (c : ℝ) (hc : 1 + Real.sqrt 2 < c) :
    ∃ (e : ℝ) (μ : PMF ℝ), 0 < e ∧
      μ.support ⊆ {0, e * (Real.sqrt 2 / 2), e, Real.sqrt 2 / 2, 1} ∧
      (∀ x ∈ μ.support, 0 ≤ x) ∧
      (6601 / 13122 : ℝ) ≤ probability μ c ∧ 1 / 2 < probability μ c := by
  obtain ⟨e, he, hQ⟩ := AboveEndpoint.exists_jump_scale c hc
  let Q := AboveEndpoint.base.addScaled AboveEndpoint.base e he.le
  have hQ' : (6601 / 13122 : ℝ) ≤ probability Q.pmf c := by
    rwa [Q.probability_eq]
  refine ⟨e, Q.pmf, he, ?_, Q.pmf_nonneg, hQ', lt_of_lt_of_le (by norm_num) hQ'⟩
  intro y hy
  rw [Q.pmf_eq_map_labels, PMF.support_map] at hy
  obtain ⟨⟨i,j⟩, _, rfl⟩ := hy
  have ha : Real.sqrt 2 / 2 ≠ (0 : ℝ) := ne_of_gt (by positivity)
  fin_cases i <;> fin_cases j <;>
    simp [Q, Law.addScaled, Law.zeroNoise, AboveEndpoint.base, AboveEndpoint.x, ha]

end Endpoint
