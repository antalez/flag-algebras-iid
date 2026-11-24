import BeatAvg.Defs

/-!
# Lemma 3.1 (substitution)

Replace the part of `μ` below `b` by a tiny scaled copy of all of `μ`. The new law cannot beat `C`.
This gives a lower bound on the successes whose target lies below `b`:
`μ⁴(success, x₃ < b) ≥ F(b)^4 P(μ) - (C - P(μ))`.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

namespace BeatAvg

/-- The substitution map: a point below `b` is replaced by `e` times an independent copy. -/
noncomputable def subst (b e : ℝ) (p : ℝ × ℝ) : ℝ := if p.1 < b then e * p.2 else p.1

theorem measurable_subst (b e : ℝ) : Measurable (subst b e) := by
  unfold subst
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) (by fun_prop)
    (by fun_prop)

theorem isLaw_subst {μ : Measure ℝ} (hμ : IsLaw μ) (b : ℝ) {e : ℝ} (he : 0 < e) :
    IsLaw ((μ.prod μ).map (subst b e)) := by
  have := hμ.prob
  refine ⟨(Measure.isProbabilityMeasure_map_iff (measurable_subst b e).aemeasurable).2
    inferInstance, ?_⟩
  rw [Measure.map_apply (measurable_subst b e) measurableSet_Iio]
  refine measure_mono_null (t := (Iio 0 ×ˢ univ) ∪ (univ ×ˢ Iio 0)) ?_ ?_
  · rintro ⟨x, y⟩ h
    simp only [mem_preimage, subst, mem_Iio] at h
    by_cases hx : x < b
    · simp only [hx, ↓reduceIte] at h
      right
      refine ⟨mem_univ _, ?_⟩
      show y < 0
      by_contra hy
      have := mul_nonneg he.le (not_lt.mp hy)
      linarith
    · simp only [hx, ↓reduceIte] at h
      left
      exact ⟨h, mem_univ _⟩
  · rw [measure_union_null_iff]
    simp [Measure.prod_prod, hμ.nonneg]

/-- Pairs of nonnegative samples. -/
def NN2 : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) := {p | (∀ i, 0 ≤ p.1 i) ∧ ∀ i, 0 ≤ p.2 i}

theorem NN2_conull {μ : Measure ℝ} (hμ : IsLaw μ) : ((iid 4 μ).prod (iid 4 μ)) NN2ᶜ = 0 := by
  have := hμ.prob
  have h0 : (iid 4 μ) {x | ∀ i, 0 ≤ x i}ᶜ = 0 := iid_nonneg_ae hμ
  refine measure_mono_null
    (t := ({x | ∀ i, 0 ≤ x i}ᶜ ×ˢ univ) ∪ (univ ×ˢ {x | ∀ i, 0 ≤ x i}ᶜ)) ?_ ?_
  · rintro ⟨x, y⟩ h
    simp only [NN2, mem_compl_iff, mem_ofPred_eq, not_and_or] at h
    rcases h with h | h
    · left; exact ⟨h, mem_univ _⟩
    · right; exact ⟨mem_univ _, h⟩
  · rw [measure_union_null_iff]
    simp [Measure.prod_prod, h0]

/-- Successes with target at least `b`. -/
def HiSet (b : ℝ) : Set (Fin 4 → ℝ) := S4 ∩ {x | b ≤ x 3}

/-- Pairs `(x, y)`: `x` succeeds with target at least `b`, with a margin that absorbs `y / (n+1)`. -/
def Dset (b : ℝ) (n : ℕ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {p | p.1 ∈ HiSet b ∧ (1 / ((n : ℝ) + 1)) * (p.2 0 + p.2 1 + p.2 2)
    < 2 * p.1 3 - (p.1 0 + p.1 1 + p.1 2)} ∩ NN2

theorem substitution {μ : Measure ℝ} (hμ : IsLaw μ) (b : ℝ) :
    (μ.real (Iio b)) ^ 4 * P μ - (C - P μ) ≤ (iid 4 μ).real (S4 ∩ {x | x 3 < b}) := by
  have := hμ.prob
  have hHi_meas : MeasurableSet (HiSet b) :=
    measurableSet_S4.inter (measurableSet_le measurable_const (measurable_pi_apply 3))
  obtain ⟨A, hAdef⟩ : ∃ A : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)), A = {x | ∀ i, x i < b} ×ˢ S4 :=
    ⟨_, rfl⟩
  have hNN2_meas : MeasurableSet NN2 := by
    have : NN2 = (⋂ i, {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | 0 ≤ p.1 i}) ∩
        ⋂ i, {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | 0 ≤ p.2 i} := by
      ext p; simp [NN2]
    rw [this]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop)).inter
      (MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop))
  have hD_meas : ∀ n, MeasurableSet (Dset b n) := by
    intro n
    have h2 : MeasurableSet {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) |
        (1 / ((n : ℝ) + 1)) * (p.2 0 + p.2 1 + p.2 2) < 2 * p.1 3 - (p.1 0 + p.1 1 + p.1 2)} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    exact ((measurable_fst hHi_meas).inter h2).inter hNN2_meas
  have hN := NN2_conull hμ
  -- the probability of `A`
  have hA : ((iid 4 μ).prod (iid 4 μ)).real A = (μ.real (Iio b)) ^ 4 * P μ := by
    have hbox : {x : Fin 4 → ℝ | ∀ i, x i < b} = univ.pi (fun _ => Iio b) := by
      ext x; simp
    simp only [Measure.real, P, hAdef, iid]
    rw [Measure.prod_prod, hbox, Measure.pi_pi]
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow, Finset.prod_const]
  -- monotonicity and union of the `D n`
  have hmono : Monotone (Dset b) := by
    intro n m hnm p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨⟨h1, lt_of_le_of_lt ?_ h2⟩, h3⟩
    have hs : 0 ≤ p.2 0 + p.2 1 + p.2 2 := by
      have := h3.2
      linarith [this 0, this 1, this 2]
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right this hs
  have hUnion : ⋃ n, Dset b n = (HiSet b ×ˢ univ) ∩ NN2 := by
    ext p
    simp only [mem_iUnion, Dset, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    constructor
    · rintro ⟨n, ⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      have hgap : 0 < 2 * p.1 3 - (p.1 0 + p.1 1 + p.1 2) := by
        have : p.1 ∈ S4 := h1.1
        simp only [S4, mem_ofPred_eq] at this
        linarith
      obtain ⟨n, hn⟩ := exists_nat_gt ((p.2 0 + p.2 1 + p.2 2) / (2 * p.1 3 - (p.1 0 + p.1 1 + p.1 2)))
      refine ⟨n, ⟨h1, ?_⟩, h3⟩
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hgap] at hn
      rw [one_div, inv_mul_lt_iff₀ hn1]
      nlinarith
  have hlim : Tendsto (fun n => ((iid 4 μ).prod (iid 4 μ)).real (Dset b n)) atTop
      (𝓝 ((iid 4 μ).real (HiSet b))) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := (iid 4 μ).prod (iid 4 μ)) hmono
    have h2 : ((iid 4 μ).prod (iid 4 μ)) (⋃ n, Dset b n) = (iid 4 μ) (HiSet b) := by
      rw [hUnion, measure_inter_conull hN, Measure.prod_prod]
      simp
    rw [h2] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  -- the inequality for each `n`
  have hstep : ∀ n : ℕ,
      (μ.real (Iio b)) ^ 4 * P μ + ((iid 4 μ).prod (iid 4 μ)).real (Dset b n) ≤ C := by
    intro n
    have he : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
    rw [← hedef] at he
    have hlaw := isLaw_subst hμ b he
    have hPle := P_le_C hlaw
    have hPeq : P ((μ.prod μ).map (subst b e)) = ((iid 4 μ).prod (iid 4 μ)).real
        {p | (fun i => subst b e (p.1 i, p.2 i)) ∈ S4} := by
      simp only [P, Measure.real, iid]
      rw [pi_map_prod_apply μ μ (subst b e) (measurable_subst b e) S4 measurableSet_S4]
    have hsub : (A ∩ NN2) ∪ Dset b n ⊆ {p | (fun i => subst b e (p.1 i, p.2 i)) ∈ S4} := by
      rintro ⟨x, y⟩ (⟨hpA, -⟩ | hpD)
      · rw [hAdef] at hpA
        obtain ⟨hx, hy⟩ := hpA
        simp only [mem_ofPred_eq] at hx
        simp only [S4, mem_ofPred_eq] at hy ⊢
        simp only [subst, hx, ↓reduceIte]
        nlinarith
      · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hpD
        obtain ⟨hS, hb⟩ := h1
        simp only [mem_ofPred_eq] at hb h2 h3 h4
        rw [← hedef] at h2
        simp only [S4, mem_ofPred_eq] at hS ⊢
        have hle : ∀ i, subst b e (x i, y i) ≤ x i + e * y i := by
          intro i
          have hx := h3 i
          have hy := mul_nonneg he.le (h4 i)
          unfold subst
          split_ifs <;> simp only [] <;> linarith
        have h3' : subst b e (x 3, y 3) = x 3 := by
          unfold subst
          simp only [not_lt.mpr hb, ↓reduceIte]
        rw [h3']
        have := hle 0
        have := hle 1
        have := hle 2
        nlinarith
    have hdisj : Disjoint (A ∩ NN2) (Dset b n) := by
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ ⟨hpA, -⟩ hpD
      rw [hAdef] at hpA
      have h1 : x 3 < b := hpA.1 3
      have h2 : b ≤ x 3 := hpD.1.1.2
      linarith
    have hAN : ((iid 4 μ).prod (iid 4 μ)).real (A ∩ NN2) = ((iid 4 μ).prod (iid 4 μ)).real A := by
      simp only [Measure.real]
      rw [measure_inter_conull hN]
    calc (μ.real (Iio b)) ^ 4 * P μ + ((iid 4 μ).prod (iid 4 μ)).real (Dset b n)
        = ((iid 4 μ).prod (iid 4 μ)).real ((A ∩ NN2) ∪ Dset b n) := by
          rw [measureReal_union hdisj (hD_meas n), hAN, hA]
      _ ≤ ((iid 4 μ).prod (iid 4 μ)).real {p | (fun i => subst b e (p.1 i, p.2 i)) ∈ S4} :=
          measureReal_mono hsub
      _ ≤ C := by rw [← hPeq]; exact hPle
  have hfinal : (μ.real (Iio b)) ^ 4 * P μ + (iid 4 μ).real (HiSet b) ≤ C :=
    le_of_tendsto' (tendsto_const_nhds.add hlim) hstep
  have hdec : P μ = (iid 4 μ).real (S4 ∩ {x | x 3 < b}) + (iid 4 μ).real (HiSet b) := by
    have hm : MeasurableSet {x : Fin 4 → ℝ | x 3 < b} :=
      measurableSet_lt (measurable_pi_apply 3) measurable_const
    have h := measureReal_inter_add_sdiff (μ := iid 4 μ) (s := S4) hm
    have hd : S4 \ {x : Fin 4 → ℝ | x 3 < b} = HiSet b := by
      ext x; simp [HiSet, not_lt]
    rw [hd] at h
    unfold P
    linarith
  linarith

end BeatAvg
