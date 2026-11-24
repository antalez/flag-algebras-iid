module
public import LeanProofs.FiniteLaw
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Endpoint

/-- Four successive independent samples from the same PMF. Each bind samples
the original PMF, regardless of the preceding values. -/
def draws4 {α : Type} (p : PMF α) : PMF (Quad α) :=
  p.bind fun a => p.bind fun b => p.bind fun d => p.map fun t => (a,b,d,t)

def mapQuad {α β : Type} (f : α → β) (a : Quad α) : Quad β :=
  (f a.1, f a.2.1, f a.2.2.1, f a.2.2.2)

theorem draws4_map {α β : Type} (p : PMF α) (f : α → β) :
    draws4 (p.map f) = (draws4 p).map (mapQuad f) := by
  simp only [draws4, PMF.bind_map, Function.comp_def, PMF.map_comp, PMF.map_bind, mapQuad]

theorem draws4_apply {α : Type} [Finite α] (p : PMF α) (a : Quad α) :
    draws4 p a = p a.1 * p a.2.1 * p a.2.2.1 * p a.2.2.2 := by
  let := Fintype.ofFinite α
  rcases a with ⟨a,b,d,t⟩
  simp only [draws4, PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  simp [ite_and, mul_ite, mul_assoc]

namespace Law
variable {α : Type} [Fintype α]

def labels (L : Law α) : PMF α :=
  PMF.ofFintype (fun i => ENNReal.ofReal (L.w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => L.w_nonneg i), L.total]
    simp)

theorem iid4_eq_draws4 (L : Law α) : L.iid4 = draws4 L.labels := by
  ext a
  rw [draws4_apply]
  simp only [iid4, PMF.ofFintype_apply, weight, labels]
  rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (L.w_nonneg _) (L.w_nonneg _)) (L.w_nonneg _)),
    ENNReal.ofReal_mul (mul_nonneg (L.w_nonneg _) (L.w_nonneg _)),
    ENNReal.ofReal_mul (L.w_nonneg _)]

theorem pmf_eq_map_labels (L : Law α) : L.pmf = L.labels.map L.x := rfl

theorem pmf_nonneg (L : Law α) : ∀ x ∈ L.pmf.support, 0 ≤ x := by
  intro x hx
  rw [pmf_eq_map_labels, PMF.support_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact L.x_nonneg i

/-- The finite combinatorial probability equals the probability for four
independent real-valued draws from the atomic law itself. -/
theorem real_event (L : Law α) (c : ℝ) :
    (draws4 L.pmf).toMeasure {a : Quad ℝ | a.1 + a.2.1 + a.2.2.1 < c * a.2.2.2} =
      ENNReal.ofReal (L.prob c) := by
  rw [pmf_eq_map_labels, draws4_map, ← iid4_eq_draws4]
  rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply_fintype]
  unfold prob
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    change (if L.wins c a then ENNReal.ofReal (L.weight a) else 0) =
      ENNReal.ofReal (if L.wins c a then L.weight a else 0)
    split_ifs <;> simp
  · intro a _
    split_ifs
    · exact L.weight_nonneg a
    · rfl

end Law
end Endpoint
