import BeatAvg.Expect

/-!
# Expectations of the degree terms, and the lower bound on the mean of the functional
-/

open MeasureTheory Set Function

namespace BeatAvg

variable {nΦ : ℕ} {Θ : Type} {D : CertData nΦ Θ} {B : ℝ}

theorem measurable_insertNth_comp {α : Type*} [MeasurableSpace α] (i : Fin 4) {fx : α → ℝ}
    {fw : α → Fin 3 → ℝ} (hx : Measurable fx) (hw : Measurable fw) :
    Measurable fun a => (Fin.insertNth i (fx a) (fw a) : Fin 4 → ℝ) := by
  refine Measurable.of_eval fun j => ?_
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa using hx
  · have : Measurable fun a => fw a k := (measurable_pi_apply k).comp hw
    simpa using this

theorem measurable_insertNth_right (i : Fin 4) (x : ℝ) :
    Measurable fun w : Fin 3 → ℝ => (Fin.insertNth i x w : Fin 4 → ℝ) :=
  measurable_insertNth_comp i measurable_const measurable_id

theorem integral_ind_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α)
    {g : α → β} (hg : Measurable g) {s : Set β} (hs : MeasurableSet s) :
    ∫ a, ind s (g a) ∂ν = ν.real (g ⁻¹' s) := by
  have : (fun a => ind s (g a)) = ind (g ⁻¹' s) := by
    funext a
    by_cases h : g a ∈ s
    · rw [ind_of_mem h, ind_of_mem (show a ∈ g ⁻¹' s from h)]
    · rw [ind_of_notMem h, ind_of_notMem (show a ∉ g ⁻¹' s from h)]
  rw [this, integral_ind _ (hg hs)]

theorem real_insertNth (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin 4) (x : ℝ) :
    (iid 3 μ).real ((fun w : Fin 3 → ℝ => (Fin.insertNth i x w : Fin 4 → ℝ)) ⁻¹' S4)
      = (iid 4 μ).real (Tset i x) := by
  have hmp := measurePreserving_comp_injective (ι := Fin 4) μ (Fin.succAbove i)
    Fin.succAbove_right_injective
  have hm : MeasurableSet ((fun w : Fin 3 → ℝ => (Fin.insertNth i x w : Fin 4 → ℝ)) ⁻¹' S4) :=
    (measurable_insertNth_comp i measurable_const measurable_id) measurableSet_S4
  have hset : (fun y : Fin 4 → ℝ => y ∘ Fin.succAbove i) ⁻¹'
      ((fun w : Fin 3 → ℝ => (Fin.insertNth i x w : Fin 4 → ℝ)) ⁻¹' S4) = Tset i x := by
    ext y
    simp only [mem_preimage, Tset, mem_ofPred_eq]
    have : (Fin.insertNth i x (y ∘ Fin.succAbove i) : Fin 4 → ℝ) = Function.update y i x := by
      funext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp
      · simp [Fin.succAbove_ne]
    rw [this]
  simp only [Measure.real]
  rw [← hset, hmp.measure_preimage hm.nullMeasurableSet]

theorem bm_s4 : BM fun p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) => s4 (p.1 0) p.2.2 := by
  show BM fun p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) =>
    ∑ i : Fin 4, ind S4 (Fin.insertNth i (p.1 0) p.2.2)
  exact BM.sum _ fun i _ => (BM.ind measurableSet_S4).comp
    (measurable_insertNth_comp i (by fun_prop) (by fun_prop))

theorem bm_s4_slice (x : ℝ) : BM fun w : Fin 3 → ℝ => s4 x w := by
  show BM fun w : Fin 3 → ℝ => ∑ i : Fin 4, ind S4 (Fin.insertNth i x w)
  exact BM.sum _ fun i _ => (BM.ind measurableSet_S4).comp
    (measurable_insertNth_comp i measurable_const measurable_id)

theorem integral_s4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ w, s4 x w ∂(iid 3 μ) = 4 * deg μ x := by
  unfold s4
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      Integrable (fun w : Fin 3 → ℝ => ind S4 (Fin.insertNth i x w)) (iid 3 μ) := fun i _ =>
    ((BM.ind measurableSet_S4).comp
      (measurable_insertNth_comp i measurable_const measurable_id)).integrable _
  rw [integral_finsetSum _ hint]
  have h : ∀ i : Fin 4, ∫ w : Fin 3 → ℝ, ind S4 (Fin.insertNth i x w) ∂(iid 3 μ)
      = (iid 4 μ).real (Tset i x) := by
    intro i
    rw [integral_ind_comp _ (measurable_insertNth_right i x) measurableSet_S4, real_insertNth]
  simp only [h]
  unfold deg
  ring

theorem bm_alo (hD : D.Valid B) :
    BM fun p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) => D.alo (p.1 0, p.2.1) :=
  (BM.of_nonneg_le hD.alo_meas hD.alo_nonneg hD.alo_le).comp (by fun_prop)

theorem bm_ahi (hD : D.Valid B) :
    BM fun p : (Fin 1 → ℝ) × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) => D.ahi (p.1 0, p.2.1) :=
  (BM.of_nonneg_le hD.ahi_meas hD.ahi_nonneg hD.ahi_le).comp (by fun_prop)

theorem bm_degLoK (hD : D.Valid B) : BM (degLoK D) :=
  (bm_alo hD).mul ((bm_s4.div_const 4).sub (BM.const D.clo))

theorem bm_degHiK (hD : D.Valid B) (x : ℝ) : BM (degHiK D x) :=
  (bm_ahi hD).mul ((BM.const x).sub (bm_s4.div_const 4))

theorem integral_s4_div (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ w, s4 x w / 4 ∂(iid 3 μ) = deg μ x := by
  rw [integral_div, integral_s4]
  ring

theorem inner_degLo (D : CertData nΦ Θ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : Fin 1 → ℝ) :
    ∫ q, degLoK D (z, q) ∂((iid 4 μ).prod (iid 3 μ))
      = (∫ s, D.alo (z 0, s) ∂(iid 4 μ)) * (deg μ (z 0) - D.clo) := by
  simp only [degLoK]
  rw [integral_prod_mul (fun s => D.alo (z 0, s)) (fun w => s4 (z 0) w / 4 - D.clo),
    integral_sub (((bm_s4_slice (z 0)).div_const 4).integrable _) (integrable_const _),
    integral_s4_div]
  simp

theorem inner_degHi (D : CertData nΦ Θ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)
    (z : Fin 1 → ℝ) :
    ∫ q, degHiK D x (z, q) ∂((iid 4 μ).prod (iid 3 μ))
      = (∫ s, D.ahi (z 0, s) ∂(iid 4 μ)) * (x - deg μ (z 0)) := by
  simp only [degHiK]
  rw [integral_prod_mul (fun s => D.ahi (z 0, s)) (fun w => x - s4 (z 0) w / 4),
    integral_sub (integrable_const _) (((bm_s4_slice (z 0)).div_const 4).integrable _),
    integral_s4_div]
  simp

theorem palo_bounds (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ ∫ s, D.alo (x, s) ∂(iid 4 μ) ∧ ∫ s, D.alo (x, s) ∂(iid 4 μ) ≤ B := by
  have hbm : BM fun s : Fin 4 → ℝ => D.alo (x, s) :=
    (BM.of_nonneg_le hD.alo_meas hD.alo_nonneg hD.alo_le).comp measurable_prodMk_left
  refine ⟨integral_nonneg fun s => hD.alo_nonneg _, ?_⟩
  have h := integral_mono (hbm.integrable (iid 4 μ)) (integrable_const B) fun s => hD.alo_le (x, s)
  simpa using h

theorem pahi_bounds (hD : D.Valid B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ ∫ s, D.ahi (x, s) ∂(iid 4 μ) ∧ ∫ s, D.ahi (x, s) ∂(iid 4 μ) ≤ B := by
  have hbm : BM fun s : Fin 4 → ℝ => D.ahi (x, s) :=
    (BM.of_nonneg_le hD.ahi_meas hD.ahi_nonneg hD.ahi_le).comp measurable_prodMk_left
  refine ⟨integral_nonneg fun s => hD.ahi_nonneg _, ?_⟩
  have h := integral_mono (hbm.integrable (iid 4 μ)) (integrable_const B) fun s => hD.ahi_le (x, s)
  simpa using h

theorem bm_deg (μ : Measure ℝ) [IsProbabilityMeasure μ] : BM (deg μ) :=
  BM.of_nonneg_le (measurable_deg μ) (deg_nonneg μ) (deg_le_one μ)

/-- Corollary 4.3, lower part. -/
theorem integral_degLo_ge (hD : D.Valid B) {μ : Measure ℝ} (hμ : IsLaw μ) {e : ℝ}
    (hdeg : ∀ x, 0 ≤ x → deg μ x ≤ P μ + e) (hclo : D.clo ≤ P μ + e) :
    -(B * e) ≤ ∫ ω, degLoK D (split3 e143 ω) ∂(iid 8 μ) := by
  have := hμ.prob
  have hmp := measurePreserving_split3 μ e143 e143_injective
  rw [integral_comp_mp hmp (bm_degLoK hD).meas, integral_prod _ ((bm_degLoK hD).integrable _)]
  have hint : Integrable (fun z => ∫ q, degLoK D (z, q) ∂((iid 4 μ).prod (iid 3 μ))) (iid 1 μ) :=
    ((bm_degLoK hD).integrable ((iid 1 μ).prod ((iid 4 μ).prod (iid 3 μ)))).integral_prod_left
  have hjbm : BM fun x => B * (deg μ x - P μ - e) :=
    (((bm_deg μ).sub (BM.const _)).sub (BM.const _)).const_mul B
  have hJ : ∫ z : Fin 1 → ℝ, B * (deg μ (z 0) - P μ - e) ∂(iid 1 μ) = -(B * e) := by
    have hev := measurePreserving_eval (fun _ : Fin 1 => μ) 0
    have h1 := integral_comp_mp hev hjbm.meas
    have h2 : ∫ x, B * (deg μ x - P μ - e) ∂μ = -(B * e) := by
      rw [integral_const_mul, integral_sub (((bm_deg μ).sub (BM.const _)).integrable _)
        (integrable_const _), integral_sub ((bm_deg μ).integrable _) (integrable_const _),
        integral_deg]
      simp
    rw [← h2, ← h1]
  rw [← hJ]
  refine integral_mono_ae ((hjbm.comp (measurable_pi_apply 0)).integrable _) hint ?_
  filter_upwards [iid_nonneg_ae (n := 1) hμ] with z hz
  show B * (deg μ (z 0) - P μ - e) ≤ ∫ q, degLoK D (z, q) ∂((iid 4 μ).prod (iid 3 μ))
  rw [inner_degLo D]
  obtain ⟨ha0, haB⟩ := palo_bounds hD μ (z 0)
  have hd := hdeg (z 0) (hz 0)
  nlinarith [mul_nonneg (sub_nonneg.2 haB) (sub_nonneg.2 hd), mul_nonneg ha0 (sub_nonneg.2 hclo)]

/-- Corollary 4.3, upper part. -/
theorem integral_degHi_ge (hD : D.Valid B) {μ : Measure ℝ} (hμ : IsLaw μ) {e x : ℝ} (he : 0 ≤ e)
    (hdeg : ∀ y, 0 ≤ y → deg μ y ≤ P μ + e) (hx : P μ ≤ x) :
    -(B * e) ≤ ∫ ω, degHiK D x (split3 e143 ω) ∂(iid 8 μ) := by
  have := hμ.prob
  have hmp := measurePreserving_split3 μ e143 e143_injective
  rw [integral_comp_mp hmp (bm_degHiK hD x).meas, integral_prod _ ((bm_degHiK hD x).integrable _)]
  have hint : Integrable (fun z => ∫ q, degHiK D x (z, q) ∂((iid 4 μ).prod (iid 3 μ)))
      (iid 1 μ) :=
    ((bm_degHiK hD x).integrable ((iid 1 μ).prod ((iid 4 μ).prod (iid 3 μ)))).integral_prod_left
  have hconst : ∫ _z : Fin 1 → ℝ, -(B * e) ∂(iid 1 μ) = -(B * e) := by simp
  rw [← hconst]
  refine integral_mono_ae (integrable_const _) hint ?_
  filter_upwards [iid_nonneg_ae (n := 1) hμ] with z hz
  show -(B * e) ≤ ∫ q, degHiK D x (z, q) ∂((iid 4 μ).prod (iid 3 μ))
  rw [inner_degHi D]
  obtain ⟨ha0, haB⟩ := pahi_bounds hD μ (z 0)
  have hd := hdeg (z 0) (hz 0)
  nlinarith [mul_nonneg ha0 (by linarith : 0 ≤ x - deg μ (z 0) + e), mul_nonneg (sub_nonneg.2 haB) he]

/-- The mean of the non-symmetrised functional at `x = C` under a nearly optimal law. -/
theorem integral_lam_ge [Fintype Θ] (hD : D.Valid B) {μ : Measure ℝ} (hμ : IsLaw μ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 36) (hP : C - ε ≤ P μ) (hclo : D.clo ≤ C) :
    C - ε - 2 * (B * (8 * Real.sqrt ε)) - (Fintype.card Θ : ℝ) * (2 * ε * B)
      ≤ ∫ ω, lam D C ω ∂(iid 8 μ) := by
  have := hμ.prob
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
  have hs6 : Real.sqrt ε ≤ 1 / 6 := by
    by_contra h
    have h' : 1 / 6 < Real.sqrt ε := not_le.mp h
    nlinarith
  have hεs : ε ≤ 8 * Real.sqrt ε := by nlinarith
  have hdeg : ∀ x, 0 ≤ x → deg μ x ≤ P μ + 8 * Real.sqrt ε :=
    fun x hx => deg_le hμ hε0 hε hP hx
  have hPC := P_le_C hμ
  -- integrability of the pieces
  have I1 : Integrable objT (iid 8 μ) := bm_objT.integrable _
  have I2 : Integrable (fun ω => sqK D (split3 e233 ω)) (iid 8 μ) :=
    ((bm_sqK hD).comp (measurePreserving_split3 μ e233 e233_injective).measurable).integrable _
  have I3 : Integrable (fun ω => degLoK D (split3 e143 ω)) (iid 8 μ) :=
    ((bm_degLoK hD).comp (measurePreserving_split3 μ e143 e143_injective).measurable).integrable _
  have I4 : Integrable (fun ω => degHiK D C (split3 e143 ω)) (iid 8 μ) :=
    ((bm_degHiK hD C).comp
      (measurePreserving_split3 μ e143 e143_injective).measurable).integrable _
  have I5 : ∀ θ, Integrable (fun ω => thr1K D θ C (split e44 ω)) (iid 8 μ) := fun θ =>
    ((bm_thr1K hD θ C).comp (measurable_split e44)).integrable _
  have I6 : ∀ θ, Integrable (fun ω => thr2K D θ (split e44 ω)) (iid 8 μ) := fun θ =>
    ((bm_thr2K hD θ).comp (measurable_split e44)).integrable _
  have I7 : Integrable (fun ω => ∑ θ, (thr1K D θ C (split e44 ω) + thr2K D θ (split e44 ω)))
      (iid 8 μ) := integrable_finsetSum _ fun θ _ => (I5 θ).add (I6 θ)
  have hsplit : ∫ ω, lam D C ω ∂(iid 8 μ) = ∫ ω, objT ω ∂(iid 8 μ)
      + ∫ ω, sqK D (split3 e233 ω) ∂(iid 8 μ) + ∫ ω, degLoK D (split3 e143 ω) ∂(iid 8 μ)
      + ∫ ω, degHiK D C (split3 e143 ω) ∂(iid 8 μ)
      + ∑ θ, (∫ ω, thr1K D θ C (split e44 ω) ∂(iid 8 μ)
        + ∫ ω, thr2K D θ (split e44 ω) ∂(iid 8 μ)) := by
    have J2 : Integrable (fun ω => objT ω + sqK D (split3 e233 ω)) (iid 8 μ) := I1.add I2
    have J3 : Integrable (fun ω => objT ω + sqK D (split3 e233 ω) + degLoK D (split3 e143 ω))
        (iid 8 μ) := J2.add I3
    have J4 : Integrable (fun ω => objT ω + sqK D (split3 e233 ω) + degLoK D (split3 e143 ω)
        + degHiK D C (split3 e143 ω)) (iid 8 μ) := J3.add I4
    have J5 : ∀ θ ∈ (Finset.univ : Finset Θ), Integrable
        (fun ω => thr1K D θ C (split e44 ω) + thr2K D θ (split e44 ω)) (iid 8 μ) :=
      fun θ _ => (I5 θ).add (I6 θ)
    simp only [lam]
    rw [integral_add J4 I7, integral_add J3 I4, integral_add J2 I3, integral_add I1 I2,
      integral_finsetSum _ J5]
    congr 1
    exact Finset.sum_congr rfl fun θ _ => integral_add (I5 θ) (I6 θ)
  have h1 := integral_objT μ
  have h2 := integral_sq_nonneg hD μ
  have h3 := integral_degLo_ge hD hμ hdeg (by linarith : D.clo ≤ P μ + 8 * Real.sqrt ε)
  have h4 := integral_degHi_ge hD hμ (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt ε) hdeg hPC
  have h5 : -((Fintype.card Θ : ℝ) * (2 * ε * B)) ≤ ∑ θ, (∫ ω, thr1K D θ C (split e44 ω) ∂(iid 8 μ)
        + ∫ ω, thr2K D θ (split e44 ω) ∂(iid 8 μ)) := by
    have hterm : ∀ θ ∈ (Finset.univ : Finset Θ), -(2 * ε * B) ≤
        ∫ ω, thr1K D θ C (split e44 ω) ∂(iid 8 μ) + ∫ ω, thr2K D θ (split e44 ω) ∂(iid 8 μ) := by
      intro θ _
      have a := integral_thr1_nonneg hD hμ θ
      have b := integral_thr2_ge hD hμ θ hε0.le hP hclo
      linarith
    have := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    linarith
  rw [hsplit]
  linarith

end BeatAvg
