module
public import Mathlib
set_option linter.style.header false
@[expose] public section

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Endpoint

/-- A finitely supported probability law on the nonnegative real axis.
The labels need not have distinct locations. -/
structure Law (α : Type) [Fintype α] where
  x : α → ℝ
  w : α → ℝ
  x_nonneg : ∀ i, 0 ≤ x i
  w_nonneg : ∀ i, 0 ≤ w i
  total : ∑ i, w i = 1

abbrev Quad (α : Type) := α × α × α × α

namespace Law
variable {α β : Type} [Fintype α] [Fintype β]

def weight (L : Law α) (a : Quad α) : ℝ :=
  L.w a.1 * L.w a.2.1 * L.w a.2.2.1 * L.w a.2.2.2

def wins (L : Law α) (c : ℝ) (a : Quad α) : Prop :=
  L.x a.1 + L.x a.2.1 + L.x a.2.2.1 < c * L.x a.2.2.2

def prob (L : Law α) (c : ℝ) : ℝ :=
  ∑ a : Quad α, if L.wins c a then L.weight a else 0

theorem weight_nonneg (L : Law α) (a : Quad α) : 0 ≤ L.weight a := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (L.w_nonneg _) (L.w_nonneg _))
    (L.w_nonneg _)) (L.w_nonneg _)

theorem weight_total (L : Law α) : ∑ a : Quad α, L.weight a = 1 := by
  simp [weight, Fintype.sum_prod_type, ← Finset.mul_sum, L.total]

theorem prob_nonneg (L : Law α) (c : ℝ) : 0 ≤ L.prob c := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact L.weight_nonneg a
  · rfl

theorem prob_le_one (L : Law α) (c : ℝ) : L.prob c ≤ 1 := by
  rw [← L.weight_total]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · rfl
  · exact L.weight_nonneg a

/-- The joint mass function of four independent draws with common weights `w`. -/
def iid4 (L : Law α) : PMF (Quad α) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (L.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => L.weight_nonneg a), L.weight_total]
    simp)

/-- The finite sum used here is literally the probability of the strict event
under the fourfold iid mass function, not an unrelated polynomial. -/
theorem iid4_event [MeasurableSpace (Quad α)] [MeasurableSingletonClass (Quad α)]
    (L : Law α) (c : ℝ) :
    L.iid4.toMeasure {a | L.wins c a} = ENNReal.ofReal (L.prob c) := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  unfold prob
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, iid4, PMF.ofFintype_apply]
    split_ifs <;> simp
  · intro a _
    split_ifs
    · exact L.weight_nonneg a
    · rfl

/-- The atomic law on the real line itself. -/
def pmf (L : Law α) : PMF ℝ :=
  (PMF.ofFintype (fun i => ENNReal.ofReal (L.w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => L.w_nonneg i), L.total]
    simp)).map L.x

theorem accepted_le (L : Law α) (c : ℝ) (A : Quad α → Prop)
    [DecidablePred A] (hA : ∀ a, A a → L.wins c a) :
    (∑ a, if A a then L.weight a else 0) ≤ L.prob c := by
  unfold prob
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : A a
  · simp [ha, hA a ha]
  · simp only [ha, ↓reduceIte]
    split_ifs
    · exact L.weight_nonneg a
    · rfl

end Law
end Endpoint
