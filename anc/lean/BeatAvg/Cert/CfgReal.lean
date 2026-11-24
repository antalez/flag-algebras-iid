import Fast.Pat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
# The configuration of a tuple of reals
-/

open MeasureTheory Set Function

namespace BeatAvg

open Classical in
/-- Order bits and sum bits of a tuple. Sum bits are recorded for distinct indices only. -/
noncomputable def cfgOf {n : ℕ} (v : Fin n → ℝ) : Fast.Cfg n :=
  ⟨fun i j => decide (v i < v j),
   fun a b c d => decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
     v a + v b + v c < 2 * v d)⟩

theorem cfgOf_comp {m n : ℕ} (v : Fin n → ℝ) (ι : Fin m → Fin n) (hι : Injective ι) :
    cfgOf (v ∘ ι) = (cfgOf v).comap ι := by
  simp only [cfgOf, Fast.Cfg.comap, comp_apply, hι.ne_iff]

instance (n : ℕ) : MeasurableSpace (Fast.Cfg n) := ⊤

theorem cfg_ext {n : ℕ} {c c' : Fast.Cfg n} (h1 : ∀ i j, c.lt i j = c'.lt i j)
    (h2 : ∀ a b e d, c.sb a b e d = c'.sb a b e d) : c = c' := by
  cases c; cases c'
  simp only [Fast.Cfg.mk.injEq]
  exact ⟨funext fun i => funext fun j => h1 i j,
    funext fun a => funext fun b => funext fun e => funext fun d => h2 a b e d⟩

instance (n : ℕ) : Finite (Fast.Cfg n) := by
  have : Injective (fun c : Fast.Cfg n => (c.lt, c.sb)) := by
    intro c c' h
    simp only [Prod.mk.injEq] at h
    exact cfg_ext (fun i j => by rw [h.1]) (fun a b e d => by rw [h.2])
  exact Finite.of_injective _ this

theorem measurableSet_decide_eq {α : Type*} [MeasurableSpace α] {p : α → Prop} [DecidablePred p]
    (hp : MeasurableSet {x | p x}) (b : Bool) : MeasurableSet {x | decide (p x) = b} := by
  cases b
  · have : {x | decide (p x) = false} = {x | p x}ᶜ := by ext x; simp
    rw [this]; exact hp.compl
  · have : {x | decide (p x) = true} = {x | p x} := by ext x; simp
    rw [this]; exact hp

theorem measurable_cfgOf {n : ℕ} : Measurable (cfgOf : (Fin n → ℝ) → Fast.Cfg n) := by
  classical
  refine measurable_to_countable' fun c => ?_
  have h : cfgOf ⁻¹' {c} = (⋂ i, ⋂ j, {v : Fin n → ℝ | decide (v i < v j) = c.lt i j}) ∩
      ⋂ a, ⋂ b, ⋂ e, ⋂ d, {v : Fin n → ℝ | decide (a ≠ b ∧ a ≠ e ∧ b ≠ e ∧ a ≠ d ∧ b ≠ d ∧ e ≠ d ∧
        v a + v b + v e < 2 * v d) = c.sb a b e d} := by
    ext v
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro rfl
      exact ⟨fun i j => rfl, fun a b e d => rfl⟩
    · rintro ⟨h1, h2⟩
      exact cfg_ext h1 h2
  rw [h]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact measurableSet_decide_eq
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)) _
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun e =>
      MeasurableSet.iInter fun d => ?_
    refine measurableSet_decide_eq ?_ _
    have hm : MeasurableSet {v : Fin n → ℝ | v a + v b + v e < 2 * v d} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    by_cases hd : a ≠ b ∧ a ≠ e ∧ b ≠ e ∧ a ≠ d ∧ b ≠ d ∧ e ≠ d
    · have : {v : Fin n → ℝ | a ≠ b ∧ a ≠ e ∧ b ≠ e ∧ a ≠ d ∧ b ≠ d ∧ e ≠ d ∧
          v a + v b + v e < 2 * v d} = {v | v a + v b + v e < 2 * v d} := by
        ext v; simp only [mem_ofPred_eq]; tauto
      rw [this]; exact hm
    · have : {v : Fin n → ℝ | a ≠ b ∧ a ≠ e ∧ b ≠ e ∧ a ≠ d ∧ b ≠ d ∧ e ≠ d ∧
          v a + v b + v e < 2 * v d} = ∅ := by
        ext v; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; tauto
      rw [this]; exact MeasurableSet.empty

/-- Any function of the configuration is measurable. -/
theorem measurable_of_cfg {n : ℕ} {β : Type*} [MeasurableSpace β] (F : Fast.Cfg n → β) :
    Measurable F := fun _ _ => trivial

end BeatAvg
