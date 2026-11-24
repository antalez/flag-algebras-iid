import BeatAvg.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bounded measurable functions, indicators, and almost sure general position
-/

open MeasureTheory Set Function

namespace BeatAvg

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Bounded measurable real functions. -/
structure BM (f : α → ℝ) : Prop where
  meas : Measurable f
  bdd : ∃ M, ∀ x, |f x| ≤ M

namespace BM

variable {f g : α → ℝ}

theorem const (c : ℝ) : BM (fun _ : α => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem add (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf.bdd
  obtain ⟨N, hN⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, M + N, fun x => (abs_add_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem neg (hf : BM f) : BM (fun x => - f x) := by
  obtain ⟨M, hM⟩ := hf.bdd
  exact ⟨hf.meas.neg, M, fun x => by rw [abs_neg]; exact hM x⟩

theorem sub (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨M, hM⟩ := hf.bdd
  obtain ⟨N, hN⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, M * N, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM x) (hN x) (abs_nonneg _) ((abs_nonneg _).trans (hM x))

theorem const_mul (c : ℝ) (hf : BM f) : BM (fun x => c * f x) := (const c).mul hf

theorem div_const (hf : BM f) (c : ℝ) : BM (fun x => f x / c) := by
  simpa [div_eq_mul_inv] using hf.mul (const c⁻¹)

theorem sum {ι : Type*} (s : Finset ι) {F : ι → α → ℝ} (h : ∀ i ∈ s, BM (F i)) :
    BM (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) 0
  | insert a s ha ih =>
    have h1 : BM (F a) := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

theorem comp {φ : β → α} (hf : BM f) (hφ : Measurable φ) : BM (fun x => f (φ x)) := by
  obtain ⟨M, hM⟩ := hf.bdd
  exact ⟨hf.meas.comp hφ, M, fun x => hM (φ x)⟩

theorem integrable (hf : BM f) (μ : Measure α) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨M, hM⟩ := hf.bdd
  exact Integrable.of_bound hf.meas.aestronglyMeasurable M (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hM x)

/-- A measurable function with values in `[0, B]`. -/
theorem of_nonneg_le (hm : Measurable f) {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) : BM f :=
  ⟨hm, B, fun x => by rw [abs_of_nonneg (h0 x)]; exact hB x⟩

end BM

/-- The `{0, 1}`-valued indicator of a set. -/
noncomputable def ind (s : Set α) : α → ℝ := s.indicator fun _ => 1

theorem ind_of_mem {s : Set α} {x : α} (h : x ∈ s) : ind s x = 1 := by simp [ind, h]

theorem ind_of_notMem {s : Set α} {x : α} (h : x ∉ s) : ind s x = 0 := by simp [ind, h]

theorem ind_nonneg (s : Set α) (x : α) : 0 ≤ ind s x := by
  by_cases h : x ∈ s
  · rw [ind_of_mem h]; exact zero_le_one
  · rw [ind_of_notMem h]

theorem ind_le_one (s : Set α) (x : α) : ind s x ≤ 1 := by
  by_cases h : x ∈ s
  · rw [ind_of_mem h]
  · rw [ind_of_notMem h]; exact zero_le_one

theorem measurable_ind {s : Set α} (hs : MeasurableSet s) : Measurable (ind s) :=
  measurable_const.indicator hs

theorem BM.ind {s : Set α} (hs : MeasurableSet s) : BM (ind s) :=
  BM.of_nonneg_le (measurable_ind hs) (ind_nonneg s) (ind_le_one s)

theorem integral_ind (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    ∫ x, ind s x ∂μ = μ.real s := by
  unfold ind
  rw [integral_indicator_const (1 : ℝ) hs]
  simp

/-- Change of variables along a measure-preserving map. -/
theorem integral_comp_mp {μ : Measure α} {ν : Measure β} {φ : α → β} (hφ : MeasurePreserving φ μ ν)
    {g : β → ℝ} (hg : Measurable g) : ∫ x, g (φ x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hφ.map_eq, integral_map hφ.aemeasurable hg.aestronglyMeasurable]

/-- General position for eight sample points: nonnegative, distinct, no ties. -/
def Generic (ω : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 ≤ ω i) ∧ Function.Injective ω ∧
    ∀ a b c d : Fin 8, a ≠ d → b ≠ d → c ≠ d → ω a + ω b + ω c ≠ 2 * ω d

/-- Lemma 1.2: a sample from an atomless law is almost surely in general position. -/
theorem ae_generic {μ : Measure ℝ} (hμ : IsLaw μ) [NullSingletonClass μ] :
    ∀ᵐ ω ∂(iid 8 μ), Generic ω := by
  have := hμ.prob
  have h1 := iid_nonneg_ae (n := 8) hμ
  have h2 : ∀ᵐ ω ∂(iid 8 μ), ∀ i j : Fin 8, i ≠ j → ω i ≠ ω j := by
    simp only [ae_all_iff]
    intro i j hij
    have h := pi_graph_null (ι := Fin 8) μ i (fun ω => ω j) (measurable_pi_apply j)
      (fun ω y => by simp [Function.update_of_ne (Ne.symm hij)])
    rw [ae_iff]
    simpa using h
  have h3 : ∀ᵐ ω ∂(iid 8 μ), ∀ a b c d : Fin 8, a ≠ d → b ≠ d → c ≠ d →
      ω a + ω b + ω c ≠ 2 * ω d := by
    simp only [ae_all_iff]
    intro a b c d had hbd hcd
    have h := pi_graph_null (ι := Fin 8) μ d (fun ω => (ω a + ω b + ω c) / 2) (by fun_prop)
      (fun ω y => by simp [Function.update_of_ne had, Function.update_of_ne hbd,
        Function.update_of_ne hcd])
    rw [ae_iff]
    refine measure_mono_null ?_ h
    intro ω hω
    simp only [mem_ofPred_eq, not_not] at hω ⊢
    linarith
  filter_upwards [h1, h2, h3] with ω g1 g2 g3
  refine ⟨g1, fun i j hij => ?_, g3⟩
  by_contra hne
  exact g2 i j hne hij

end BeatAvg
