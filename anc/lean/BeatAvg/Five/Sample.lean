import BeatAvg.Five.ScalarExpectation
import BeatAvg.Five.Families

/-! Five-point sample terms and their expectations. -/
open MeasureTheory Set Function
namespace BeatAvg.Five
open Fast.Five

noncomputable def pairClass (p : ℝ × ℝ) : ℕ :=
  if p.1 < p.2 then (if p.2 < 2*p.1 then 2 else 0)
  else (if p.1 < 2*p.2 then 3 else 1)

noncomputable def pairWeight (p : ℝ × ℝ) : ℝ := (Data.nu[pairClass p]?.getD 0 : ℚ)

theorem pairWeight_bounds (p : ℝ × ℝ) : 0 ≤ pairWeight p ∧ pairWeight p ≤ 6 := by
  unfold pairWeight pairClass
  split_ifs <;> norm_num [Data.nu]

theorem bm_pairWeight : BM pairWeight := by
  apply BM.of_nonneg_le _ (fun p => (pairWeight_bounds p).1) (fun p => (pairWeight_bounds p).2)
  have hdef : pairWeight = fun p : ℝ × ℝ =>
      if p.1 < p.2 then (if p.2 < 2*p.1 then (5807278/1000000 : ℝ) else 3991657/1000000)
      else (if p.1 < 2*p.2 then 2176036/1000000 else 3991657/1000000) := by
    funext p
    unfold pairWeight pairClass
    split_ifs <;> norm_num [Data.nu]
  rw [hdef]
  apply Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const measurable_const

def e14 : Fin 1 ⊕ Fin 4 → Fin 5 := finSumFinEquiv

def e113 : Fin 1 ⊕ (Fin 1 ⊕ Fin 3) → Fin 5 :=
  fun s => finSumFinEquiv (Sum.map id finSumFinEquiv s)

def splitTail (ω : Fin 5 → ℝ) : ℝ × (Fin 4 → ℝ) :=
  ((split e14 ω).1 0, (split e14 ω).2)

def splitDegree (ω : Fin 5 → ℝ) : ℝ × (ℝ × (Fin 3 → ℝ)) :=
  ((split3 e113 ω).1 0, ((split3 e113 ω).2.1 0, (split3 e113 ω).2.2))

theorem e113_injective : Injective e113 :=
  finSumFinEquiv.injective.comp (Sum.map_injective.mpr ⟨injective_id, finSumFinEquiv.injective⟩)

theorem splitTail_mp (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving splitTail (iid 5 μ) (μ.prod (iid 4 μ)) :=
  ((measurePreserving_eval (fun _ : Fin 1 => μ) 0).prod (MeasurePreserving.id (iid 4 μ))).comp
    (measurePreserving_split μ e14 finSumFinEquiv.injective)

theorem splitDegree_mp (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving splitDegree (iid 5 μ) (μ.prod (μ.prod (iid 3 μ))) :=
  ((measurePreserving_eval (fun _ : Fin 1 => μ) 0).prod
    ((measurePreserving_eval (fun _ : Fin 1 => μ) 0).prod (MeasurePreserving.id (iid 3 μ)))).comp
    (measurePreserving_split3 μ e113 e113_injective)

def firstFour : Fin 4 → Fin 5 := fun i => ⟨i.val, by omega⟩

noncomputable def objective (ω : Fin 5 → ℝ) : ℝ := ind S4 (ω ∘ firstFour)

theorem bm_objective : BM objective := (BM.ind measurableSet_S4).comp (by fun_prop)

theorem integral_objective (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ ω, objective ω ∂(iid 5 μ) = P μ := by
  have hi : Injective firstFour := by
    intro i j h
    exact Fin.ext (congrArg (Fin.val : Fin 5 → ℕ) h)
  rw [show objective = fun ω => ind S4 (ω ∘ firstFour) from rfl,
    integral_comp_mp (measurePreserving_comp_injective μ firstFour hi) (measurable_ind measurableSet_S4),
    integral_ind _ measurableSet_S4]
  rfl

theorem integral_sample_degree {μ : Measure ℝ} (hμ : IsLaw μ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1/36) (hP : C-ε ≤ P μ) (hB : Bstar ≤ C) :
    -(48*Real.sqrt ε) ≤ ∫ ω, degreeTerm pairWeight Bstar (splitDegree ω) ∂(iid 5 μ) := by
  have := hμ.prob
  rw [integral_comp_mp (splitDegree_mp μ) (bm_degreeTerm bm_pairWeight Bstar).meas]
  convert integral_degreeTerm_lower hμ bm_pairWeight
    (fun p => (pairWeight_bounds p).1) (fun p => (pairWeight_bounds p).2) hε0 hε hP hB using 1 <;> ring

theorem integral_sample_tail {μ : Measure ℝ} (hμ : IsLaw μ) (q : ℝ) :
    0 ≤ ∫ ω, tailTerm q C (splitTail ω) ∂(iid 5 μ) := by
  have := hμ.prob
  rw [integral_comp_mp (splitTail_mp μ) (bm_tailTerm q C).meas]
  exact integral_tailTerm_nonneg hμ q

end BeatAvg.Five
