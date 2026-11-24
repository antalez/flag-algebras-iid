import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

/-!
# General lemmas on finite product measures

Marginals along injective reindexings, splitting a product measure into blocks,
and negligibility of graphs.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace BeatAvg

variable {X : Type*} [MeasurableSpace X]

/-- Marginal of a product of probability measures along an injective reindexing. -/
theorem pi_map_comp_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → Measure X) [∀ i, IsProbabilityMeasure (m i)] (e : κ → ι) (he : Injective e) :
    (Measure.pi m).map (fun ω : ι → X => ω ∘ e) = Measure.pi (fun k => m (e k)) := by
  classical
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun ω : ι → X => ω ∘ e) :=
    Measurable.of_eval fun k => measurable_pi_apply (e k)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let t : ι → Set X := fun i => ⋂ k, ⋂ (_ : e k = i), s k
  have hpre : (fun ω : ι → X => ω ∘ e) ⁻¹' (univ.pi s) = univ.pi t := by
    ext ω
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, comp_apply, t, mem_iInter]
    constructor
    · intro h i k hk; subst hk; exact h k
    · intro h k; exact h (e k) k rfl
  rw [hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective e he _ _ ?_ ?_
  · intro i hi
    have : t i = univ := by
      apply eq_univ_of_forall
      intro x
      simp only [t, mem_iInter]
      intro k hk
      exact absurd ⟨k, hk⟩ hi
    rw [this, measure_univ]
  · intro k
    have : t (e k) = s k := by
      ext x
      simp only [t, mem_iInter]
      constructor
      · intro h; exact h k rfl
      · intro h k' hk'; rw [he hk']; exact h
    rw [this]

/-- Reindexing invariance of an iid product. -/
theorem measurePreserving_comp_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : κ → ι) (he : Injective e) :
    MeasurePreserving (fun ω : ι → X => ω ∘ e) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : κ => μ) :=
  ⟨Measurable.of_eval fun k => measurable_pi_apply (e k),
    pi_map_comp_injective (fun _ => μ) e he⟩

/-- Splitting an iid sample indexed by `ι` into two blocks along `e : α ⊕ β → ι`. -/
def split {ι α β : Type*} (e : α ⊕ β → ι) (ω : ι → X) : (α → X) × (β → X) :=
  (fun a => ω (e (Sum.inl a)), fun b => ω (e (Sum.inr b)))

theorem measurable_split {ι α β : Type*} (e : α ⊕ β → ι) :
    Measurable (split (X := X) e) :=
  (Measurable.of_eval fun a => measurable_pi_apply (e (Sum.inl a))).prodMk
    (Measurable.of_eval fun b => measurable_pi_apply (e (Sum.inr b)))

theorem measurePreserving_split {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : α ⊕ β → ι) (he : Injective e) :
    MeasurePreserving (split (X := X) e) (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_comp_injective μ e he
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => X) (fun _ => μ)
  exact h2.comp h1

/-- Splitting an iid sample into three blocks. -/
def split3 {ι α β γ : Type*} (e : α ⊕ (β ⊕ γ) → ι) (ω : ι → X) :
    (α → X) × ((β → X) × (γ → X)) :=
  (fun a => ω (e (Sum.inl a)),
    (fun b => ω (e (Sum.inr (Sum.inl b))), fun c => ω (e (Sum.inr (Sum.inr c)))))

theorem measurePreserving_split3 {ι α β γ : Type*} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : α ⊕ (β ⊕ γ) → ι) (he : Injective e) :
    MeasurePreserving (split3 (X := X) e) (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod
        ((Measure.pi fun _ : β => μ).prod (Measure.pi fun _ : γ => μ))) := by
  have h1 := measurePreserving_split μ e he
  have h2 := measurePreserving_split μ (id : β ⊕ γ → β ⊕ γ) injective_id
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : α => μ)).prod h2
  exact h3.comp h1

/-- Resampling one coordinate of an iid sample. -/
theorem map_update_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure X)
    [IsProbabilityMeasure μ] (i : ι) :
    (μ.prod (Measure.pi fun _ : ι => μ)).map
        (fun p : X × (ι → X) => Function.update p.2 i p.1)
      = Measure.pi fun _ : ι => μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun p : X × (ι → X) => Function.update p.2 i p.1) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j = i
    · subst h; simpa using measurable_fst
    · have h2 : Measurable (fun c : X × (ι → X) => c.2 j) := by fun_prop
      simpa [Function.update_of_ne h] using h2
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : X × (ι → X) => Function.update p.2 i p.1) ⁻¹' (univ.pi s)
      = (s i) ×ˢ (univ.pi (Function.update s i univ)) := by
    ext ⟨y, ω⟩
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j; simpa [Function.update_of_ne hj] using this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · have := h2 j; simpa [Function.update_of_ne hj] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hupd : ∀ j, μ (Function.update s i univ j) = Function.update (fun j => μ (s j)) i 1 j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [hupd]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul, Finset.sdiff_singleton_eq_erase,
    Finset.mul_prod_erase Finset.univ (fun j => μ (s j)) (Finset.mem_univ i)]

theorem measurePreserving_update {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure X)
    [IsProbabilityMeasure μ] (i : ι) :
    MeasurePreserving (fun p : X × (ι → X) => Function.update p.2 i p.1)
      (μ.prod (Measure.pi fun _ : ι => μ)) (Measure.pi fun _ : ι => μ) := by
  refine ⟨?_, map_update_prod μ i⟩
  refine Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · subst h; simpa using measurable_fst
  · have h2 : Measurable (fun c : X × (ι → X) => c.2 j) := by fun_prop
    simpa [Function.update_of_ne h] using h2

/-- For an atomless law, an iid sample almost surely avoids the graph of a function of the
other coordinates. -/
theorem pi_graph_null {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (i : ι) (g : (ι → ℝ) → ℝ) (hg : Measurable g)
    (hindep : ∀ ω y, g (Function.update ω i y) = g ω) :
    Measure.pi (fun _ : ι => μ) {ω | ω i = g ω} = 0 := by
  have hA : MeasurableSet {ω : ι → ℝ | ω i = g ω} :=
    measurableSet_eq_fun (measurable_pi_apply i) hg
  have hmp := measurePreserving_update μ i
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hA,
    Measure.prod_apply_symm (hmp.measurable hA)]
  have : ∀ ω : ι → ℝ, μ ((fun y => (y, ω)) ⁻¹'
      ((fun p : ℝ × (ι → ℝ) => Function.update p.2 i p.1) ⁻¹' {ω | ω i = g ω})) = 0 := by
    intro ω
    have : ((fun y => (y, ω)) ⁻¹'
      ((fun p : ℝ × (ι → ℝ) => Function.update p.2 i p.1) ⁻¹' {ω | ω i = g ω})) = {g ω} := by
      ext y
      simp [hindep]
    rw [this]
    exact measure_singleton _
  rw [lintegral_congr this, lintegral_zero]

/-- Product of a constant multiple of a measure. -/
theorem pi_smul_const {ι : Type*} [Fintype ι] (c : ℝ≥0∞) (ν : Measure X) [SigmaFinite ν]
    [SigmaFinite (c • ν)] :
    Measure.pi (fun _ : ι => c • ν) = c ^ Fintype.card ι • Measure.pi (fun _ : ι => ν) := by
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

/-- An iid sample from the image of a product law `μ ⊗ U` under `h` is the coordinatewise image of
a pair of independent iid samples from `μ` and from `U`. -/
theorem pi_map_prod_apply {ι : Type*} [Fintype ι] {Y Z : Type*} [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (U : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure U] (h : X × Y → Z) (hh : Measurable h) (A : Set (ι → Z))
    (hA : MeasurableSet A) :
    Measure.pi (fun _ : ι => (μ.prod U).map h) A =
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => U))
        {p | (fun i => h (p.1 i, p.2 i)) ∈ A} := by
  have hprob : IsProbabilityMeasure ((μ.prod U).map h) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 inferInstance
  rw [← Measure.pi_map_pi (fun _ => hh.aemeasurable), Measure.map_apply (by fun_prop) hA]
  have hmp := measurePreserving_arrowProdEquivProdArrow X Y ι (fun _ => μ) (fun _ => U)
  rw [← hmp.measure_preimage_equiv]
  rfl

end BeatAvg
