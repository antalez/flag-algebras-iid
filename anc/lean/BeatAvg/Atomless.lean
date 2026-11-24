import BeatAvg.Defs

/-!
# Lemma 1.1 (atomless laws suffice) and Lemma 1.2 (no ties)
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

namespace BeatAvg

/-- Uniform law on `[0, 1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif, Real.volume_Icc]⟩

instance : NullSingletonClass unif := by unfold unif; infer_instance

theorem unif_Icc_compl : unif (Icc 0 1)ᶜ = 0 := by
  simp [unif, Measure.restrict_apply measurableSet_Icc.compl]

/-- Smoothing map. -/
def smooth (d : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + d * p.2

theorem measurable_smooth (d : ℝ) : Measurable (smooth d) := by unfold smooth; fun_prop

theorem isLaw_smooth {μ : Measure ℝ} (hμ : IsLaw μ) {d : ℝ} (hd : 0 ≤ d) :
    IsLaw ((μ.prod unif).map (smooth d)) := by
  have := hμ.prob
  refine ⟨(Measure.isProbabilityMeasure_map_iff (measurable_smooth d).aemeasurable).2
    inferInstance, ?_⟩
  rw [Measure.map_apply (measurable_smooth d) measurableSet_Iio]
  refine measure_mono_null (t := (Iio 0 ×ˢ univ) ∪ (univ ×ˢ (Icc 0 1)ᶜ)) ?_ ?_
  · rintro ⟨x, u⟩ h
    simp only [mem_preimage, smooth, mem_Iio] at h
    by_cases hx : x < 0
    · left; exact ⟨hx, mem_univ _⟩
    · right
      refine ⟨mem_univ _, ?_⟩
      intro hu
      have := mul_nonneg hd hu.1
      linarith [not_lt.mp hx]
  · rw [measure_union_null_iff]
    simp [Measure.prod_prod, hμ.nonneg, unif_Icc_compl]

theorem nullSingleton_smooth {μ : Measure ℝ} (hμ : IsLaw μ) {d : ℝ} (hd : 0 < d) :
    NullSingletonClass ((μ.prod unif).map (smooth d)) := by
  have := hμ.prob
  refine ⟨fun z => ?_⟩
  rw [Measure.map_apply (measurable_smooth d) (measurableSet_singleton z),
    Measure.prod_apply ((measurable_smooth d) (measurableSet_singleton z))]
  have : ∀ x : ℝ, unif (Prod.mk x ⁻¹' (smooth d ⁻¹' {z})) = 0 := by
    intro x
    refine measure_mono_null (t := {(z - x) / d}) ?_ (measure_singleton _)
    intro u hu
    simp only [mem_preimage, smooth, mem_singleton_iff] at hu ⊢
    field_simp
    linarith
  rw [lintegral_congr this, lintegral_zero]

/-- Samples with a margin `3 d` in the success inequality. -/
def Gset (n : ℕ) : Set (Fin 4 → ℝ) := {x | x 0 + x 1 + x 2 + 3 * (1 / ((n : ℝ) + 1)) < 2 * x 3}

theorem smooth_lower {μ : Measure ℝ} (hμ : IsLaw μ) (n : ℕ) :
    (iid 4 μ).real (Gset n) ≤ P ((μ.prod unif).map (smooth (1 / ((n : ℝ) + 1)))) := by
  have := hμ.prob
  have hd : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  simp only [P, Measure.real, iid]
  rw [pi_map_prod_apply μ unif (smooth _) (measurable_smooth _) S4 measurableSet_S4]
  have hM : (Measure.pi fun _ : Fin 4 => unif) (univ.pi fun _ => Icc (0 : ℝ) 1)ᶜ = 0 := by
    have h1 : (Measure.pi fun _ : Fin 4 => unif) (univ.pi fun _ => Icc (0 : ℝ) 1) = 1 := by
      rw [Measure.pi_pi]
      have : unif (Icc 0 1) = 1 := by simp [unif, Real.volume_Icc]
      simp [this]
    rw [measure_compl (MeasurableSet.univ_pi fun _ => measurableSet_Icc) (measure_ne_top _ _), h1]
    simp
  have hsub : Gset n ×ˢ (univ.pi fun _ => Icc (0 : ℝ) 1) ⊆
      {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) |
        (fun i => smooth (1 / ((n : ℝ) + 1)) (p.1 i, p.2 i)) ∈ S4} := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    simp only [Gset, mem_ofPred_eq] at hx
    simp only [S4, mem_ofPred_eq, smooth]
    have h0 : u 0 ∈ Icc (0 : ℝ) 1 := hu 0 (mem_univ _)
    have h1 : u 1 ∈ Icc (0 : ℝ) 1 := hu 1 (mem_univ _)
    have h2 : u 2 ∈ Icc (0 : ℝ) 1 := hu 2 (mem_univ _)
    have h3 : u 3 ∈ Icc (0 : ℝ) 1 := hu 3 (mem_univ _)
    have e0 := mul_le_mul_of_nonneg_left h0.2 hd.le
    have e1 := mul_le_mul_of_nonneg_left h1.2 hd.le
    have e2 := mul_le_mul_of_nonneg_left h2.2 hd.le
    have e3 := mul_nonneg hd.le h3.1
    linarith
  have hval : ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => unif))
      (Gset n ×ˢ (univ.pi fun _ => Icc (0 : ℝ) 1)) = (iid 4 μ) (Gset n) := by
    rw [Measure.prod_prod, Measure.pi_pi]
    have : unif (Icc 0 1) = 1 := by simp [unif, Real.volume_Icc]
    simp [this]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  calc (iid 4 μ) (Gset n) = _ := hval.symm
    _ ≤ _ := measure_mono hsub

/-- Lemma 1.1: atomless laws come arbitrarily close to any law. -/
theorem exists_atomless {μ : Measure ℝ} (hμ : IsLaw μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : Measure ℝ, IsLaw ν ∧ NullSingletonClass ν ∧ P μ - ε < P ν := by
  have := hμ.prob
  have hmono : Monotone Gset := by
    intro n m hnm x hx
    simp only [Gset, mem_ofPred_eq] at hx ⊢
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hUnion : ⋃ n, Gset n = S4 := by
    ext x
    simp only [mem_iUnion, Gset, S4, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      have hgap : 0 < 2 * x 3 - (x 0 + x 1 + x 2) := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (3 / (2 * x 3 - (x 0 + x 1 + x 2)))
      refine ⟨n, ?_⟩
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hgap] at hn
      have : 3 * (1 / ((n : ℝ) + 1)) < 2 * x 3 - (x 0 + x 1 + x 2) := by
        rw [mul_one_div, div_lt_iff₀ hn1]
        nlinarith
      linarith
  have hlim : Tendsto (fun n => (iid 4 μ).real (Gset n)) atTop (𝓝 (P μ)) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := iid 4 μ) hmono
    rw [hUnion] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have hev : ∀ᶠ n in atTop, P μ - ε < (iid 4 μ).real (Gset n) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := hev.exists
  have hd : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨_, isLaw_smooth hμ hd.le, nullSingleton_smooth hμ hd, lt_of_lt_of_le hn (smooth_lower hμ n)⟩

/-- Atomless laws whose value is within `ε` of `C`. -/
theorem exists_atomless_law_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : Measure ℝ, IsLaw ν ∧ NullSingletonClass ν ∧ C - ε < P ν := by
  obtain ⟨μ, hμ, h1⟩ := exists_law_gt (half_pos hε)
  obtain ⟨ν, hν, hna, h2⟩ := exists_atomless hμ (half_pos hε)
  exact ⟨ν, hν, hna, by linarith⟩

end BeatAvg
