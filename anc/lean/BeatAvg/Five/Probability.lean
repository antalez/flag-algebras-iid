import BeatAvg.ExpectDeg
import BeatAvg.Atomless
import BeatAvg.Five.Generic

/-! Probability lemmas for the five-point route. The degree estimate and atomless
approximation are reused from the original proof. -/
open MeasureTheory Set Function
namespace BeatAvg.Five

/-- The lower-degree inequality for any bounded measurable weight. This is the
one-root form of the old `integral_degLo_ge`, independent of sample size. -/
theorem weighted_degree_lower {μ : Measure ℝ} (hμ : IsLaw μ)
    {a : ℝ → ℝ} (ha : BM a) {M b e : ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (haM : ∀ x, a x ≤ M)
    (hdeg : ∀ x, 0 ≤ x → deg μ x ≤ P μ + e) (hb : b ≤ P μ + e) :
    -(M * e) ≤ ∫ x, a x * (deg μ x - b) ∂μ := by
  have := hμ.prob
  have hleft : BM fun x => M * (deg μ x - P μ - e) :=
    (((bm_deg μ).sub (BM.const _)).sub (BM.const _)).const_mul M
  have hright : BM fun x => a x * (deg μ x - b) :=
    ha.mul ((bm_deg μ).sub (BM.const _))
  have heq : ∫ x, M * (deg μ x - P μ - e) ∂μ = -(M * e) := by
    rw [integral_const_mul, integral_sub (((bm_deg μ).sub (BM.const _)).integrable _)
      (integrable_const _), integral_sub ((bm_deg μ).integrable _) (integrable_const _),
      integral_deg]
    simp
  rw [← heq]
  refine integral_mono_ae (hleft.integrable _) (hright.integrable _) ?_
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simpa only [Set.Iio_def, not_le] using hμ.nonneg
  filter_upwards [hnonneg] with x hx
  have hd := hdeg x hx
  nlinarith [mul_nonneg (sub_nonneg.2 (haM x)) (sub_nonneg.2 hd),
    mul_nonneg (ha0 x) (sub_nonneg.2 hb)]

/-- The same quantitative error as in the old proof, for a new pair-color
weight bounded by M. -/
theorem weighted_degree_near_optimal {μ : Measure ℝ} (hμ : IsLaw μ)
    {a : ℝ → ℝ} (ha : BM a) {M b ε : ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (haM : ∀ x, a x ≤ M)
    (hε0 : 0 < ε) (hε : ε ≤ 1/36) (hP : C - ε ≤ P μ) (hb : b ≤ C) :
    -(M * (8 * Real.sqrt ε)) ≤ ∫ x, a x * (deg μ x - b) ∂μ := by
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
  have hsmall : Real.sqrt ε ≤ 1/6 := by nlinarith
  apply weighted_degree_lower hμ ha ha0 haM
    (fun x hx => deg_le hμ hε0 hε hP hx)
  nlinarith

/-- A sample-size-independent version of the original two-point criterion.
The caller supplies the expectation bound assembled from the certificate terms. -/
theorem C_le_of_functional {n : ℕ} (L : ℝ → (Fin n → ℝ) → ℝ)
    {b δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hbm : ∀ x, BM (L x))
    (haff : ∀ x y s ω, L ((1-s)*x+s*y) ω = (1-s)*L x ω+s*L y ω)
    (hb : ∀ ω, Generic ω → L b ω ≤ b)
    (h1 : ∀ ω, Generic ω → L 1 ω ≤ 1-δ)
    (hmean : ∀ (μ : Measure ℝ), IsLaw μ → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/36 → C-ε ≤ P μ → b ≤ C →
      C-ε-K*Real.sqrt ε ≤ ∫ ω, L C ω ∂(iid n μ)) : C ≤ b := by
  by_contra hc
  have hbc : b < C := not_le.mp hc
  have hb1 : b < 1 := hbc.trans_le C_le_one
  let s := (C-b)/(1-b)
  have hs0 : 0 < s := div_pos (sub_pos.mpr hbc) (sub_pos.mpr hb1)
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hb1)).mpr (by linarith [C_le_one])
  have hceq : C = (1-s)*b+s*1 := by
    dsimp [s]
    have hn : 1-b ≠ 0 := (sub_pos.mpr hb1).ne'
    field_simp
    nlinarith
  have hupper : ∀ ω, Generic ω → L C ω ≤ C-s*δ := by
    intro ω hω
    have hh := haff b 1 s ω
    rw [← hceq] at hh
    rw [hh]
    have hh0 := mul_le_mul_of_nonneg_left (hb ω hω) (sub_nonneg.mpr hs1)
    have hh1 := mul_le_mul_of_nonneg_left (h1 ω hω) hs0.le
    nlinarith
  let t := min (1/6 : ℝ) (s*δ/(2*(1+K)))
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos (mul_pos hs0 hδ) (by linarith))
  have ht6 : t ≤ 1/6 := min_le_left _ _
  have hterr : t*(2*(1+K)) ≤ s*δ :=
    (le_div_iff₀ (by linarith : 0 < 2*(1+K))).mp (min_le_right _ _)
  have he0 : 0 < t^2 := sq_pos_of_pos ht0
  have he : t^2 ≤ 1/36 := by nlinarith
  obtain ⟨μ, hμ, hatom, hp⟩ := exists_atomless_law_gt he0
  have := hμ.prob
  have hlow := hmean μ hμ (t^2) he0 he hp.le hbc.le
  rw [Real.sqrt_sq ht0.le] at hlow
  have hup : ∫ ω, L C ω ∂(iid n μ) ≤ C-s*δ := by
    have hh := integral_mono_ae ((hbm C).integrable (iid n μ)) (integrable_const (C-s*δ))
      ((ae_generic hμ).mono fun ω hω => hupper ω hω)
    simpa using hh
  have htt : t^2 ≤ t := by nlinarith
  have hpos : 0 < s*δ := mul_pos hs0 hδ
  nlinarith

end BeatAvg.Five
