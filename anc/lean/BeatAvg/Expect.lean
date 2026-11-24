import BeatAvg.Sample
import BeatAvg.Sublaw
import BeatAvg.Substitution

/-!
# Expectations of the terms of the eight-point functional
-/

open MeasureTheory Set Function

namespace BeatAvg

variable {nΦ : ℕ} {Θ : Type} {D : CertData nΦ Θ} {B : ℝ}

/-! ### Objective term -/

theorem bm_objT : BM objT :=
  (BM.ind measurableSet_S4).comp (measurable_split e44).fst

theorem integral_objT (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ ω, objT ω ∂(iid 8 μ) = P μ := by
  have hmp := measurePreserving_comp_injective (ι := Fin 8) μ (e44 ∘ Sum.inl)
    (e44_injective.comp Sum.inl_injective)
  have h : ∀ ω : Fin 8 → ℝ, objT ω = ind S4 (ω ∘ (e44 ∘ Sum.inl)) := fun ω => rfl
  simp only [h]
  rw [integral_comp_mp hmp (measurable_ind measurableSet_S4), integral_ind _ measurableSet_S4]
  rfl

/-! ### Square term -/

/-- The set of (roots, triple) with flag `i`. -/
def Fi (D : CertData nΦ Θ) (i : Fin nΦ) : Set ((Fin 2 → ℝ) × (Fin 3 → ℝ)) := {q | D.flag q = i}

theorem measurableSet_Fi (hD : D.Valid B) (i : Fin nΦ) : MeasurableSet (Fi D i) :=
  hD.flag_meas (measurableSet_singleton i)

theorem ind_Fi (D : CertData nΦ Θ) (i : Fin nΦ) (q : (Fin 2 → ℝ) × (Fin 3 → ℝ)) :
    ind (Fi D i) q = if D.flag q = i then 1 else 0 := by
  by_cases h : D.flag q = i
  · rw [ind_of_mem (show q ∈ Fi D i from h), if_pos h]
  · rw [ind_of_notMem (show q ∉ Fi D i from h), if_neg h]

theorem sqK_eq (D : CertData nΦ Θ) (p : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :
    sqK D p = ∑ i, ∑ j, ind (Fi D i) (p.1, p.2.1) * D.Q i j * ind (Fi D j) (p.1, p.2.2) := by
  simp only [ind_Fi, sqK]
  simp [Finset.sum_ite_eq, ite_mul, mul_ite]

theorem bm_sqK (hD : D.Valid B) : BM (sqK D) := by
  have h : sqK D = fun p => ∑ i, ∑ j,
      ind (Fi D i) (p.1, p.2.1) * D.Q i j * ind (Fi D j) (p.1, p.2.2) := funext (sqK_eq D)
  rw [h]
  refine BM.sum _ fun i _ => BM.sum _ fun j _ => ?_
  have h1 : BM fun p : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => ind (Fi D i) (p.1, p.2.1) :=
    (BM.ind (measurableSet_Fi hD i)).comp (by fun_prop)
  have h2 : BM fun p : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => ind (Fi D j) (p.1, p.2.2) :=
    (BM.ind (measurableSet_Fi hD j)).comp (by fun_prop)
  exact (h1.mul (BM.const _)).mul h2

theorem integral_sq_nonneg (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, sqK D (split3 e233 ω) ∂(iid 8 μ) := by
  have hmp := measurePreserving_split3 μ e233 e233_injective
  rw [integral_comp_mp hmp (bm_sqK hD).meas, integral_prod _ ((bm_sqK hD).integrable _)]
  refine integral_nonneg fun r => ?_
  show 0 ≤ ∫ q, sqK D (r, q) ∂((iid 3 μ).prod (iid 3 μ))
  simp only [sqK_eq]
  have hint : ∀ i j, Integrable (fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ind (Fi D i) (r, q.1) * D.Q i j * ind (Fi D j) (r, q.2)) ((iid 3 μ).prod (iid 3 μ)) := by
    intro i j
    have h1 : BM fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ind (Fi D i) (r, q.1) :=
      (BM.ind (measurableSet_Fi hD i)).comp (by fun_prop)
    have h2 : BM fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ind (Fi D j) (r, q.2) :=
      (BM.ind (measurableSet_Fi hD j)).comp (by fun_prop)
    exact ((h1.mul (BM.const _)).mul h2).integrable _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have hterm : ∀ i j, ∫ q, ind (Fi D i) (r, q.1) * D.Q i j * ind (Fi D j) (r, q.2)
      ∂((iid 3 μ).prod (iid 3 μ)) = (∫ t, ind (Fi D i) (r, t) ∂(iid 3 μ)) * D.Q i j *
        (∫ t, ind (Fi D j) (r, t) ∂(iid 3 μ)) := by
    intro i j
    rw [integral_prod_mul (fun t => ind (Fi D i) (r, t) * D.Q i j) (fun t => ind (Fi D j) (r, t)),
      integral_mul_const]
  have hsum : ∀ i, ∫ q, ∑ j, ind (Fi D i) (r, q.1) * D.Q i j * ind (Fi D j) (r, q.2)
      ∂((iid 3 μ).prod (iid 3 μ)) = ∑ j, (∫ t, ind (Fi D i) (r, t) ∂(iid 3 μ)) * D.Q i j *
        (∫ t, ind (Fi D j) (r, t) ∂(iid 3 μ)) := by
    intro i
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  simp only [hsum]
  exact hD.Q_psd fun i => ∫ t, ind (Fi D i) (r, t) ∂(iid 3 μ)

/-! ### Threshold terms -/

theorem measurableSet_A1 (hD : D.Valid B) (θ : Θ) : MeasurableSet (A1 D θ) := by
  have : A1 D θ = ⋂ i, {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | p.2 i < D.τ θ p.1} := by
    ext p; simp [A1]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt (by fun_prop) ((hD.τ_meas θ).comp measurable_fst)

theorem measurableSet_A2 (hD : D.Valid B) (θ : Θ) : MeasurableSet (A2 D θ) :=
  (measurable_snd measurableSet_S4).inter (measurableSet_A1 hD θ)

theorem measurableSet_A3 (hD : D.Valid B) (θ : Θ) : MeasurableSet (A3 D θ) :=
  (measurable_snd measurableSet_S4).inter
    (measurableSet_lt (by fun_prop) ((hD.τ_meas θ).comp measurable_fst))

theorem bm_u1 (hD : D.Valid B) (θ : Θ) :
    BM fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => D.u1 θ p.1 :=
  (BM.of_nonneg_le (hD.u1_meas θ) (hD.u1_nonneg θ) (hD.u1_le θ)).comp measurable_fst

theorem bm_u2 (hD : D.Valid B) (θ : Θ) :
    BM fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => D.u2 θ p.1 :=
  (BM.of_nonneg_le (hD.u2_meas θ) (hD.u2_nonneg θ) (hD.u2_le θ)).comp measurable_fst

theorem bm_thr1K (hD : D.Valid B) (θ : Θ) (x : ℝ) : BM (thr1K D θ x) :=
  (bm_u1 hD θ).mul (((BM.ind (measurableSet_A1 hD θ)).const_mul x).sub
    (BM.ind (measurableSet_A2 hD θ)))

theorem bm_thr2K (hD : D.Valid B) (θ : Θ) : BM (thr2K D θ) :=
  (bm_u2 hD θ).mul ((BM.ind (measurableSet_A3 hD θ)).sub
    ((BM.ind (measurableSet_A1 hD θ)).const_mul D.clo))

/-- Integrating an indicator over the second variable. -/
theorem integral_ind_slice {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure β)
    {s : Set (α × β)} (hs : MeasurableSet s) (a : α) :
    ∫ b, ind s (a, b) ∂ν = ν.real (Prod.mk a ⁻¹' s) := by
  have : (fun b => ind s (a, b)) = ind (Prod.mk a ⁻¹' s) := by
    funext b
    by_cases h : (a, b) ∈ s
    · rw [ind_of_mem h, ind_of_mem (show b ∈ Prod.mk a ⁻¹' s from h)]
    · rw [ind_of_notMem h, ind_of_notMem (show b ∉ Prod.mk a ⁻¹' s from h)]
  rw [this, integral_ind _ (measurable_prodMk_left hs)]

theorem real_box (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    (iid 4 μ).real {f | ∀ i, f i < b} = (μ.real (Iio b)) ^ 4 := by
  have hbox : {x : Fin 4 → ℝ | ∀ i, x i < b} = univ.pi (fun _ => Iio b) := by
    ext x; simp
  simp only [Measure.real, iid]
  rw [hbox, Measure.pi_pi]
  simp [ENNReal.toReal_pow, Finset.prod_const]

theorem inner_thr1 (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : Θ) (x : ℝ)
    (ρ : Fin 4 → ℝ) :
    ∫ f, thr1K D θ x (ρ, f) ∂(iid 4 μ) = D.u1 θ ρ *
      (x * (μ.real (Iio (D.τ θ ρ))) ^ 4 - (iid 4 μ).real (S4 ∩ {f | ∀ i, f i < D.τ θ ρ})) := by
  have h1 : Integrable (fun f => x * ind (A1 D θ) (ρ, f)) (iid 4 μ) :=
    (((BM.ind (measurableSet_A1 hD θ)).const_mul x).comp measurable_prodMk_left).integrable _
  have h2 : Integrable (fun f => ind (A2 D θ) (ρ, f)) (iid 4 μ) :=
    ((BM.ind (measurableSet_A2 hD θ)).comp measurable_prodMk_left).integrable _
  simp only [thr1K]
  rw [integral_const_mul, integral_sub h1 h2, integral_const_mul,
    integral_ind_slice _ (measurableSet_A1 hD θ), integral_ind_slice _ (measurableSet_A2 hD θ)]
  have e1 : Prod.mk ρ ⁻¹' A1 D θ = {f | ∀ i, f i < D.τ θ ρ} := rfl
  have e2 : Prod.mk ρ ⁻¹' A2 D θ = S4 ∩ {f | ∀ i, f i < D.τ θ ρ} := rfl
  rw [e1, e2, real_box]

theorem inner_thr2 (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : Θ)
    (ρ : Fin 4 → ℝ) :
    ∫ f, thr2K D θ (ρ, f) ∂(iid 4 μ) = D.u2 θ ρ *
      ((iid 4 μ).real (S4 ∩ {f | f 3 < D.τ θ ρ}) - D.clo * (μ.real (Iio (D.τ θ ρ))) ^ 4) := by
  have h1 : Integrable (fun f => ind (A3 D θ) (ρ, f)) (iid 4 μ) :=
    ((BM.ind (measurableSet_A3 hD θ)).comp measurable_prodMk_left).integrable _
  have h2 : Integrable (fun f => D.clo * ind (A1 D θ) (ρ, f)) (iid 4 μ) :=
    (((BM.ind (measurableSet_A1 hD θ)).const_mul D.clo).comp measurable_prodMk_left).integrable _
  simp only [thr2K]
  rw [integral_const_mul, integral_sub h1 h2, integral_const_mul,
    integral_ind_slice _ (measurableSet_A1 hD θ), integral_ind_slice _ (measurableSet_A3 hD θ)]
  have e1 : Prod.mk ρ ⁻¹' A1 D θ = {f | ∀ i, f i < D.τ θ ρ} := rfl
  have e3 : Prod.mk ρ ⁻¹' A3 D θ = S4 ∩ {f | f 3 < D.τ θ ρ} := rfl
  rw [e1, e3, real_box]

theorem integral_thr1_nonneg (hD : D.Valid B) {μ : Measure ℝ} (hμ : IsLaw μ) (θ : Θ) :
    0 ≤ ∫ ω, thr1K D θ C (split e44 ω) ∂(iid 8 μ) := by
  have := hμ.prob
  have hmp := measurePreserving_split μ e44 e44_injective
  rw [integral_comp_mp hmp (bm_thr1K hD θ C).meas, integral_prod _ ((bm_thr1K hD θ C).integrable _)]
  refine integral_nonneg fun ρ => ?_
  show 0 ≤ ∫ f, thr1K D θ C (ρ, f) ∂(iid 4 μ)
  rw [inner_thr1 hD]
  exact mul_nonneg (hD.u1_nonneg θ ρ) (sub_nonneg.2 (sublaw hμ _))

theorem integral_thr2_ge (hD : D.Valid B) {μ : Measure ℝ} (hμ : IsLaw μ) (θ : Θ) {ε : ℝ}
    (hε : 0 ≤ ε) (hP : C - ε ≤ P μ) (hclo : D.clo ≤ C) :
    -(2 * ε * B) ≤ ∫ ω, thr2K D θ (split e44 ω) ∂(iid 8 μ) := by
  have := hμ.prob
  have hmp := measurePreserving_split μ e44 e44_injective
  rw [integral_comp_mp hmp (bm_thr2K hD θ).meas, integral_prod _ ((bm_thr2K hD θ).integrable _)]
  have hint : Integrable (fun ρ => ∫ f, thr2K D θ (ρ, f) ∂(iid 4 μ)) (iid 4 μ) :=
    ((bm_thr2K hD θ).integrable ((iid 4 μ).prod (iid 4 μ))).integral_prod_left
  have hconst : ∫ _ρ : Fin 4 → ℝ, -(2 * ε * B) ∂(iid 4 μ) = -(2 * ε * B) := by simp
  rw [← hconst]
  refine integral_mono (integrable_const _) hint fun ρ => ?_
  show -(2 * ε * B) ≤ ∫ f, thr2K D θ (ρ, f) ∂(iid 4 μ)
  rw [inner_thr2 hD]
  have hsub := substitution hμ (D.τ θ ρ)
  have hF0 : 0 ≤ (μ.real (Iio (D.τ θ ρ))) ^ 4 := by positivity
  have hF1 : (μ.real (Iio (D.τ θ ρ))) ^ 4 ≤ 1 := pow_le_one₀ measureReal_nonneg measureReal_le_one
  have hu0 := hD.u2_nonneg θ ρ
  have hu1 := hD.u2_le θ ρ
  have hPC := P_le_C hμ
  -- the bracket is at least `-2 ε`
  have hbr : -(2 * ε) ≤ (iid 4 μ).real (S4 ∩ {f | f 3 < D.τ θ ρ})
      - D.clo * (μ.real (Iio (D.τ θ ρ))) ^ 4 := by
    have h1 : -ε ≤ (μ.real (Iio (D.τ θ ρ))) ^ 4 * (P μ - D.clo) := by
      by_cases hs : 0 ≤ P μ - D.clo
      · have := mul_nonneg hF0 hs
        linarith
      · have hs' : P μ - D.clo ≤ 0 := (not_le.mp hs).le
        have : (P μ - D.clo) ≤ (μ.real (Iio (D.τ θ ρ))) ^ 4 * (P μ - D.clo) := by nlinarith
        linarith
    nlinarith
  have hB0 : 0 ≤ B := (hD.u2_nonneg θ ρ).trans (hD.u2_le θ ρ)
  by_cases hs : 0 ≤ (iid 4 μ).real (S4 ∩ {f | f 3 < D.τ θ ρ})
      - D.clo * (μ.real (Iio (D.τ θ ρ))) ^ 4
  · have := mul_nonneg hu0 hs
    nlinarith
  · have hs' := (not_le.mp hs).le
    nlinarith

end BeatAvg
