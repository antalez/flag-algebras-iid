import BeatAvg.Lower.Count
import Mathlib.MeasureTheory.Measure.Interval

/-!
# One step of the paper's construction

The paper puts a copy of the law at a smaller scale next to each atom: `Y = X + η Y'`, with
`X ~ ν` and `Y'` an independent copy of `Y` (proof of the proposition on strict inequalities).
Here `Y'` has an arbitrary law `lam` on `[0, ∞)`; then

`P(law of X + η Y') ≥ p^4 P(lam) + E[Ff] - 4 δ`

as soon as `η` is small enough: when all four `X_i` are `0` the inequality for the `Y_i` is the
inequality for the `Y_i'`, and on the events of `Ff` the margin `2^{-N}` absorbs `η Y'`.
-/

open MeasureTheory Set Filter Topology

namespace BeatAvg.Lower

variable {p : ℝ} {N : ℕ}

/-- The atom of index `q.1`, plus `η` times an independent draw. -/
noncomputable def mix (N : ℕ) (η : ℝ) (q : Fin (N + 1) × ℝ) : ℝ := val q.1 + η * q.2

theorem measurable_mix (η : ℝ) : Measurable (mix N η) := by
  have h : Measurable (val (N := N)) := Measurable.of_discrete
  unfold mix
  exact (h.comp measurable_fst).add (measurable_snd.const_mul η)

/-- The law of `X + η Y'`. -/
noncomputable def mixLaw (p : ℝ) (N : ℕ) (η : ℝ) (lam : Measure ℝ) : Measure ℝ :=
  ((gridM p N).prod lam).map (mix N η)

theorem isLaw_mixLaw (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    {lam : Measure ℝ} (hl : IsLaw lam) : IsLaw (mixLaw p N η lam) := by
  have := gridM_prob hp0 hp1 hN
  have := hl.prob
  refine ⟨(Measure.isProbabilityMeasure_map_iff (measurable_mix η).aemeasurable).2 inferInstance,
    ?_⟩
  unfold mixLaw
  rw [Measure.map_apply (measurable_mix η) measurableSet_Iio]
  refine measure_mono_null (t := univ ×ˢ Iio 0) ?_ ?_
  · rintro ⟨j, y⟩ h
    simp only [mem_preimage, mix, mem_Iio] at h
    refine ⟨mem_univ _, ?_⟩
    show y < 0
    by_contra hy
    have h1 := mul_nonneg hη.le (not_lt.mp hy)
    have h2 := val_nonneg j
    linarith
  · rw [Measure.prod_prod, hl.nonneg, mul_zero]

/-- Samples with all coordinates in `[0, A]`. -/
def YA (A : ℝ) : Set (Fin 4 → ℝ) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ A}

theorem YA_eq (A : ℝ) : YA A = univ.pi fun _ : Fin 4 => Icc 0 A := by
  ext y
  simp only [YA, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left, mem_Icc]

theorem measurableSet_YA (A : ℝ) : MeasurableSet (YA A) := by
  rw [YA_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The success event for the four mixed variables. -/
def Emix (N : ℕ) (η : ℝ) : Set ((Fin 4 → Fin (N + 1)) × (Fin 4 → ℝ)) :=
  {q | (fun i => mix N η (q.1 i, q.2 i)) ∈ S4}

theorem measurableSet_Emix (η : ℝ) : MeasurableSet (Emix N η) := by
  have hm : Measurable fun q : (Fin 4 → Fin (N + 1)) × (Fin 4 → ℝ) =>
      (fun i => mix N η (q.1 i, q.2 i)) := by
    refine Measurable.of_eval fun i => (measurable_mix η).comp ?_
    exact ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  exact hm measurableSet_S4

/-- The indicator inequality of the paper, for the present law. -/
theorem pointwise {η A : ℝ} (hη : 0 < η) (hA : 3 * η * A < (1 / 2 : ℝ) ^ N)
    (k : Fin 4 → Fin (N + 1)) (y : Fin 4 → ℝ) :
    zf (k 0) * zf (k 1) * zf (k 2) * zf (k 3) * ind S4 y + Ff k * ind (YA A) y
      ≤ ind (Emix N η) (k, y) := by
  classical
  have hF := Ff_le k
  have hF0 := Ff_nonneg k
  by_cases hall : ∀ i, (k i : ℕ) = 0
  · -- all four at the atom `0`
    have hgap : ¬ Gap k := by
      unfold Gap
      rw [val_zero (hall 0), val_zero (hall 1), val_zero (hall 2), val_zero (hall 3)]
      have : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
      linarith
    rw [if_neg hgap] at hF
    have hFz : Ff k = 0 := le_antisymm hF hF0
    simp only [zf, hall, if_true, one_mul, hFz, zero_mul, add_zero]
    by_cases hy : y ∈ S4
    · have : (k, y) ∈ Emix N η := by
        simp only [Emix, S4, mem_ofPred_eq, mix] at hy ⊢
        rw [val_zero (hall 0), val_zero (hall 1), val_zero (hall 2), val_zero (hall 3)]
        nlinarith
      rw [ind_of_mem hy, ind_of_mem this]
    · rw [ind_of_notMem hy]; exact ind_nonneg _ _
  · -- not all at `0`
    have hz : zf (k 0) * zf (k 1) * zf (k 2) * zf (k 3) = 0 := by
      obtain ⟨i, hi⟩ := not_forall.1 hall
      fin_cases i <;> simp_all [zf]
    rw [hz, zero_mul, zero_add]
    by_cases hg : Gap k
    · rw [if_pos hg] at hF
      by_cases hy : y ∈ YA A
      · have : (k, y) ∈ Emix N η := by
          simp only [Emix, S4, mem_ofPred_eq, mix]
          unfold Gap at hg
          have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3
          have e : η * y 0 + η * y 1 + η * y 2 ≤ 3 * η * A := by nlinarith
          have e3 : 0 ≤ η * y 3 := mul_nonneg hη.le h3.1
          linarith
        rw [ind_of_mem hy, ind_of_mem this, mul_one]; exact hF
      · rw [ind_of_notMem hy, mul_zero]; exact ind_nonneg _ _
    · rw [if_neg hg] at hF
      have hFz : Ff k = 0 := le_antisymm hF hF0
      rw [hFz, zero_mul]; exact ind_nonneg _ _

/-- A law on `[0, ∞)` gives mass at least `1 - δ` to some `[0, A]`. -/
theorem exists_mass {lam : Measure ℝ} (hl : IsLaw lam) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ 1 - δ ≤ lam.real (Icc 0 A) := by
  have := hl.prob
  have h1 : Tendsto (fun x => lam.real (Iic x)) atTop (𝓝 1) := by
    have h := tendsto_measure_Iic_atTop lam
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top lam univ)).comp h
    rw [measure_univ, ENNReal.toReal_one] at h2
    exact h2
  have h2 : ∀ᶠ x in atTop, 1 - δ < lam.real (Iic x) := h1.eventually (lt_mem_nhds (by linarith))
  obtain ⟨A, hA1, hA2⟩ := (h2.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨A, hA2, ?_⟩
  have hsub : Iic A ⊆ Icc 0 A ∪ Iio 0 := by
    intro x hx
    by_cases h0 : 0 ≤ x
    · left; exact ⟨h0, hx⟩
    · right; exact not_le.mp h0
  have h3 : lam.real (Iic A) ≤ lam.real (Icc 0 A) + lam.real (Iio 0) :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have h4 : lam.real (Iio 0) = 0 := by simp [Measure.real, hl.nonneg]
  linarith

/-- **One step.** For every law `lam` there is a law whose success probability is at least
`p^4 P(lam) + E[Ff] - 4 δ`. -/
theorem one_step (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) {lam : Measure ℝ} (hl : IsLaw lam)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ μ : Measure ℝ, IsLaw μ ∧
      p ^ 4 * P lam + (∫ k, Ff k ∂(Measure.pi fun _ : Fin 4 => gridM p N)) - 4 * δ ≤ P μ := by
  have hm := gridM_prob hp0 hp1 hN
  have := hl.prob
  obtain ⟨A, hA0, hA⟩ := exists_mass hl hδ
  -- the scale
  obtain ⟨η, hη, hηA⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η * A < (1 / 2 : ℝ) ^ N := by
    have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
    refine ⟨(1 / 2 : ℝ) ^ N / (4 * A), by positivity, ?_⟩
    have : 3 * ((1 / 2 : ℝ) ^ N / (4 * A)) * A = 3 / 4 * (1 / 2 : ℝ) ^ N := by
      field_simp
    rw [this]; linarith
  refine ⟨mixLaw p N η lam, isLaw_mixLaw hp0 hp1 hN hη hl, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : Measure ((Fin 4 → Fin (N + 1)) × (Fin 4 → ℝ)),
      M = (Measure.pi fun _ : Fin 4 => gridM p N).prod (iid 4 lam) := ⟨_, rfl⟩
  have hMp : IsProbabilityMeasure M := by rw [hM]; infer_instance
  -- the success probability of the new law, on the product space
  have hP : P (mixLaw p N η lam) = M.real (Emix N η) := by
    unfold P iid mixLaw Measure.real
    rw [pi_map_prod_apply (gridM p N) lam (mix N η) (measurable_mix η) S4 measurableSet_S4, hM]
    rfl
  -- the two parts of the lower bound
  obtain ⟨g1, hg1⟩ : ∃ g : (Fin 4 → Fin (N + 1)) → ℝ,
      g = fun k => zf (k 0) * zf (k 1) * zf (k 2) * zf (k 3) := ⟨_, rfl⟩
  have bm1 : BM fun q : (Fin 4 → Fin (N + 1)) × (Fin 4 → ℝ) => g1 q.1 * ind S4 q.2 := by
    have hb : BM g1 := ⟨Measurable.of_discrete, by
      have := Finite.bddAbove_range fun k => |g1 k|
      obtain ⟨B, hB⟩ := this
      exact ⟨B, fun k => hB ⟨k, rfl⟩⟩⟩
    exact (hb.comp measurable_fst).mul ((BM.ind measurableSet_S4).comp measurable_snd)
  have bm2 : BM fun q : (Fin 4 → Fin (N + 1)) × (Fin 4 → ℝ) => Ff q.1 * ind (YA A) q.2 := by
    have hb : BM (Ff (N := N)) := ⟨Measurable.of_discrete, by
      have := Finite.bddAbove_range fun k : Fin 4 → Fin (N + 1) => |Ff k|
      obtain ⟨B, hB⟩ := this
      exact ⟨B, fun k => hB ⟨k, rfl⟩⟩⟩
    exact (hb.comp measurable_fst).mul ((BM.ind (measurableSet_YA A)).comp measurable_snd)
  have hle : ∫ q, (g1 q.1 * ind S4 q.2 + Ff q.1 * ind (YA A) q.2) ∂M ≤ ∫ q, ind (Emix N η) q ∂M := by
    refine integral_mono ((bm1.add bm2).integrable M) ((BM.ind (measurableSet_Emix η)).integrable M)
      fun q => ?_
    rw [hg1]
    exact pointwise hη hηA q.1 q.2
  rw [integral_add (bm1.integrable M) (bm2.integrable M), integral_ind M (measurableSet_Emix η),
    ← hP, hM, integral_prod_mul, integral_prod_mul, integral_ind _ measurableSet_S4,
    integral_ind _ (measurableSet_YA A)] at hle
  -- the first part
  have e1 : ∫ k, g1 k ∂(Measure.pi fun _ : Fin 4 => gridM p N) = p ^ 4 := by
    rw [hg1, int4, int_zf hp0 hp1]; ring
  -- the mass of the box
  have e2 : (iid 4 lam).real (YA A) = (lam.real (Icc 0 A)) ^ 4 := by
    simp only [Measure.real, iid, YA_eq]
    rw [Measure.pi_pi]
    simp [ENNReal.toReal_pow, Finset.prod_const]
  -- the mean of `Ff` is in `[0, 1]`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ k, Ff k ∂(Measure.pi fun _ : Fin 4 => gridM p N) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact integral_nonneg fun k => Ff_nonneg k
  have ha1 : a ≤ 1 := by
    classical
    rw [ha]
    have h1 : ∀ k : Fin 4 → Fin (N + 1), Ff k ≤ 1 := fun k =>
      (Ff_le k).trans (by split_ifs <;> norm_num)
    have := integral_mono (μ := Measure.pi fun _ : Fin 4 => gridM p N) Integrable.of_finite
      (integrable_const (1 : ℝ)) h1
    simpa using this
  rw [e1, e2, ← ha] at hle
  have hr1 : lam.real (Icc 0 A) ≤ 1 := measureReal_le_one
  have hr4 : 1 - 4 * δ ≤ (lam.real (Icc 0 A)) ^ 4 := by
    have h1 : (1 - δ) ^ 4 ≤ (lam.real (Icc 0 A)) ^ 4 := pow_le_pow_left₀ (by linarith) hA 4
    have h2 : 1 - 4 * δ ≤ (1 - δ) ^ 4 := by nlinarith [sq_nonneg δ, sq_nonneg (1 - δ)]
    linarith
  have hr41 : (lam.real (Icc 0 A)) ^ 4 ≤ 1 := pow_le_one₀ measureReal_nonneg hr1
  unfold P at hle ⊢
  rw [← ha]
  nlinarith

end BeatAvg.Lower
