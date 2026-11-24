import BeatAvg.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Degree regularity (Lemmas 4.1, 4.2)

`deg μ x` is the success probability when one of the four positions is fixed at `x`, averaged over
the position. Mixing a small atom at `x` into `μ` cannot beat `C`, which bounds `deg μ x`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace BeatAvg

/-- Samples that succeed once coordinate `i` is replaced by `x`. -/
def Tset (i : Fin 4) (x : ℝ) : Set (Fin 4 → ℝ) := {y | Function.update y i x ∈ S4}

theorem measurable_update_fun (i : Fin 4) (x : ℝ) :
    Measurable (fun y : Fin 4 → ℝ => Function.update y i x) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simpa [Function.update_of_ne h] using measurable_pi_apply j

theorem measurableSet_Tset (i : Fin 4) (x : ℝ) : MeasurableSet (Tset i x) :=
  measurable_update_fun i x measurableSet_S4

/-- The degree of `x`: average over the position `i` of the probability of success with the
`i`-th point fixed at `x`. -/
noncomputable def deg (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (1 / 4) * ∑ i : Fin 4, (iid 4 μ).real (Tset i x)

theorem deg_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ deg μ x := by
  unfold deg
  have : 0 ≤ ∑ i : Fin 4, (iid 4 μ).real (Tset i x) := Finset.sum_nonneg fun i _ => measureReal_nonneg
  linarith

theorem deg_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : deg μ x ≤ 1 := by
  unfold deg
  have : ∑ i : Fin 4, (iid 4 μ).real (Tset i x) ≤ ∑ _i : Fin 4, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => measureReal_le_one
  simp at this
  linarith

/-- Bernoulli law on `Bool`. -/
noncomputable def bern (t : ℝ) : Measure Bool :=
  ENNReal.ofReal t • Measure.dirac true + ENNReal.ofReal (1 - t) • Measure.dirac false

theorem bern_prob {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsProbabilityMeasure (bern t) :=
  ⟨by simp [bern, ← ENNReal.ofReal_add ht0 (sub_nonneg.2 ht1)]⟩

theorem bern_true (t : ℝ) : bern t {true} = ENNReal.ofReal t := by simp [bern]

theorem bern_false (t : ℝ) : bern t {false} = ENNReal.ofReal (1 - t) := by simp [bern]

/-- Mixing map: the point is replaced by `x` when the label is `true`. -/
def mixmap (x : ℝ) (p : ℝ × Bool) : ℝ := if p.2 then x else p.1

theorem measurable_mixmap (x : ℝ) : Measurable (mixmap x) := by
  unfold mixmap
  exact Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
    measurable_fst

theorem isLaw_mix {μ : Measure ℝ} (hμ : IsLaw μ) {x : ℝ} (hx : 0 ≤ x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : IsLaw ((μ.prod (bern t)).map (mixmap x)) := by
  have := hμ.prob
  have := bern_prob ht0 ht1
  refine ⟨(Measure.isProbabilityMeasure_map_iff (measurable_mixmap x).aemeasurable).2
    inferInstance, ?_⟩
  rw [Measure.map_apply (measurable_mixmap x) measurableSet_Iio]
  refine measure_mono_null (t := Iio 0 ×ˢ univ) ?_ (by simp [Measure.prod_prod, hμ.nonneg])
  rintro ⟨y, u⟩ h
  simp only [mem_preimage, mixmap, mem_Iio] at h
  cases u
  · simpa using h
  · simp at h; linarith

/-- Labels: `none` = no point replaced, `some i` = exactly the `i`-th point replaced. -/
def uvec (o : Option (Fin 4)) : Fin 4 → Bool := fun j => decide (o = some j)

theorem uvec_injective : Function.Injective uvec := by
  intro o o' h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some i' => have := congrFun h i'; simp [uvec] at this
  | some i =>
    have := congrFun h i
    simp [uvec] at this
    exact this.symm ▸ rfl

/-- The sample events attached to the labels. -/
def Tfam (x : ℝ) (o : Option (Fin 4)) : Set (Fin 4 → ℝ) := o.elim S4 fun i => Tset i x

theorem measurableSet_Tfam (x : ℝ) (o : Option (Fin 4)) : MeasurableSet (Tfam x o) := by
  cases o with
  | none => exact measurableSet_S4
  | some i => exact measurableSet_Tset i x

theorem pi_bern_uvec {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (o : Option (Fin 4)) :
    (Measure.pi fun _ : Fin 4 => bern t).real {uvec o}
      = o.elim ((1 - t) ^ 4) fun _ => t * (1 - t) ^ 3 := by
  have := bern_prob ht0 ht1
  have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
  simp only [Measure.real, Measure.pi_singleton]
  cases o with
  | none =>
    simp [uvec, bern_false, Finset.prod_const, ENNReal.toReal_pow, ENNReal.toReal_ofReal h1t]
  | some i =>
    fin_cases i <;>
    simp [uvec, bern_false, bern_true, Fin.prod_univ_four, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal h1t, ENNReal.toReal_ofReal ht0] <;> ring

/-- Lemma 4.2, before optimising the weight: mixing an atom at `x` with weight `t`. -/
theorem mix_lower {μ : Measure ℝ} (hμ : IsLaw μ) {x : ℝ} (hx : 0 ≤ x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (1 - t) ^ 4 * P μ + 4 * t * (1 - t) ^ 3 * deg μ x ≤ C := by
  have := hμ.prob
  have := bern_prob ht0 ht1
  have hlaw := isLaw_mix hμ hx ht0 ht1
  have hPle := P_le_C hlaw
  have hPeq : P ((μ.prod (bern t)).map (mixmap x)) =
      ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => bern t)).real
        {p | (fun i => mixmap x (p.1 i, p.2 i)) ∈ S4} := by
    simp only [P, Measure.real, iid]
    rw [pi_map_prod_apply μ (bern t) (mixmap x) (measurable_mixmap x) S4 measurableSet_S4]
  have hsub : (⋃ o, Tfam x o ×ˢ {uvec o}) ⊆
      {p : (Fin 4 → ℝ) × (Fin 4 → Bool) | (fun i => mixmap x (p.1 i, p.2 i)) ∈ S4} := by
    intro p hp
    simp only [mem_iUnion, mem_prod, mem_singleton_iff] at hp
    obtain ⟨o, hy, hu⟩ := hp
    obtain ⟨y, u⟩ := p
    simp only at hy hu
    subst hu
    cases o with
    | none =>
      have : (fun i => mixmap x (y i, uvec none i)) = y := by
        funext i; simp [mixmap, uvec]
      simp only [mem_ofPred_eq, this]
      exact hy
    | some i =>
      have : (fun j => mixmap x (y j, uvec (some i) j)) = Function.update y i x := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [mixmap, uvec]
        · have : ¬ i = j := fun h => hj h.symm
          simp [mixmap, uvec, Function.update_of_ne hj, this]
      simp only [mem_ofPred_eq, this]
      exact hy
  have hdisj : Pairwise (Disjoint on fun o => Tfam x o ×ˢ ({uvec o} : Set (Fin 4 → Bool))) := by
    intro o o' hoo'
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨y, u⟩ ⟨-, hu⟩ ⟨-, hu'⟩
    simp only [mem_singleton_iff] at hu hu'
    exact hoo' (uvec_injective (hu.symm.trans hu'))
  have hmeas : ∀ o, MeasurableSet (Tfam x o ×ˢ ({uvec o} : Set (Fin 4 → Bool))) :=
    fun o => (measurableSet_Tfam x o).prod (measurableSet_singleton _)
  have hval : ∀ o, ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => bern t)).real
      (Tfam x o ×ˢ {uvec o}) = (iid 4 μ).real (Tfam x o) *
        o.elim ((1 - t) ^ 4) fun _ => t * (1 - t) ^ 3 := by
    intro o
    rw [← pi_bern_uvec ht0 ht1 o]
    simp only [Measure.real]
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hsum : ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => bern t)).real
      (⋃ o, Tfam x o ×ˢ {uvec o}) = (1 - t) ^ 4 * P μ + 4 * t * (1 - t) ^ 3 * deg μ x := by
    rw [measureReal_iUnion_fintype hdisj hmeas, Fintype.sum_option, hval none]
    have hs : ∀ i : Fin 4, ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => bern t)).real
        (Tfam x (some i) ×ˢ {uvec (some i)}) = (iid 4 μ).real (Tset i x) * (t * (1 - t) ^ 3) :=
      fun i => hval (some i)
    simp only [hs]
    rw [← Finset.sum_mul]
    simp only [Tfam, Option.elim]
    unfold deg P
    ring
  calc (1 - t) ^ 4 * P μ + 4 * t * (1 - t) ^ 3 * deg μ x
      = ((iid 4 μ).prod (Measure.pi fun _ : Fin 4 => bern t)).real
          (⋃ o, Tfam x o ×ˢ {uvec o}) := hsum.symm
    _ ≤ _ := measureReal_mono hsub
    _ ≤ C := by rw [← hPeq]; exact hPle

/-- Lemma 4.2: a nearly optimal law has degree at most `P(μ) + 8 √ε` everywhere. -/
theorem deg_le {μ : Measure ℝ} (hμ : IsLaw μ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 36)
    (hP : C - ε ≤ P μ) {x : ℝ} (hx : 0 ≤ x) : deg μ x ≤ P μ + 8 * Real.sqrt ε := by
  have := hμ.prob
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt ε := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.sqrt_pos.2 hε0
  have htsq : t ^ 2 = ε := by rw [htdef]; exact Real.sq_sqrt hε0.le
  have ht6 : t ≤ 1 / 6 := by
    by_contra h
    have h' : 1 / 6 < t := not_le.mp h
    nlinarith
  have h := mix_lower hμ hx ht0.le (by linarith : t ≤ 1)
  have hP0 := P_nonneg μ
  have hP1 := P_le_one μ
  have hd0 := deg_nonneg μ x
  rw [← htdef]
  -- 4 t (1-3t) d ≤ 4 t (1-t)^3 d ≤ C - (1-t)^4 P ≤ 4 t P + t^2
  have h1 : (1 - t) ^ 3 ≥ 1 - 3 * t := by nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) ht0.le]
  have h2 : 1 - (1 - t) ^ 4 ≤ 4 * t := by nlinarith [sq_nonneg t, sq_nonneg (t * t), sq_nonneg (1 - t), mul_nonneg ht0.le (sq_nonneg t)]
  have h3 : 4 * t * (1 - 3 * t) * deg μ x ≤ 4 * t * P μ + t ^ 2 := by
    have ha : 4 * t * (1 - 3 * t) * deg μ x ≤ 4 * t * (1 - t) ^ 3 * deg μ x := by
      have : 0 ≤ 4 * t * deg μ x := by positivity
      nlinarith
    have hb : (1 - (1 - t) ^ 4) * P μ ≤ 4 * t * P μ := mul_le_mul_of_nonneg_right h2 hP0
    nlinarith
  have h4 : (1 - 3 * t) * deg μ x ≤ P μ + t / 4 := by
    have : 4 * t * ((1 - 3 * t) * deg μ x) ≤ 4 * t * (P μ + t / 4) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  by_contra hcon
  have hcon' : P μ + 8 * t < deg μ x := not_le.mp hcon
  have h5 : (1 - 3 * t) * (P μ + 8 * t) ≤ (1 - 3 * t) * deg μ x :=
    mul_le_mul_of_nonneg_left hcon'.le (by linarith)
  nlinarith

/-! ### The mean of the degree is `P(μ)` -/

theorem measurable_measure_Tset (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin 4) :
    Measurable fun x => (iid 4 μ) (Tset i x) :=
  measurable_measure_prodMk_left (ν := iid 4 μ)
    ((measurePreserving_update μ i).measurable measurableSet_S4)

theorem lintegral_Tset (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin 4) :
    ∫⁻ x, (iid 4 μ) (Tset i x) ∂μ = (iid 4 μ) S4 := by
  have hmp := measurePreserving_update μ i
  rw [← hmp.measure_preimage measurableSet_S4.nullMeasurableSet,
    Measure.prod_apply (hmp.measurable measurableSet_S4)]
  rfl

theorem measurable_real_Tset (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin 4) :
    Measurable fun x => (iid 4 μ).real (Tset i x) :=
  (measurable_measure_Tset μ i).ennreal_toReal

theorem integrable_real_Tset (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : Fin 4) :
    Integrable (fun x => (iid 4 μ).real (Tset i x)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_real_Tset μ i).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem measurable_deg (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measurable (deg μ) := by
  unfold deg
  exact (Finset.measurable_sum _ fun i _ => measurable_real_Tset μ i).const_mul _

theorem integral_deg (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∫ x, deg μ x ∂μ = P μ := by
  unfold deg
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_real_Tset μ i]
  have h : ∀ i : Fin 4, ∫ x, (iid 4 μ).real (Tset i x) ∂μ = P μ := by
    intro i
    simp only [Measure.real]
    rw [integral_toReal (measurable_measure_Tset μ i).aemeasurable
      (ae_of_all _ fun x => measure_lt_top _ _), lintegral_Tset]
    rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

end BeatAvg
