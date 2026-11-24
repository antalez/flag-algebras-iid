import BeatAvg.Five.Probability

/-! The scalar terms use the original sublaw and degree theorems. Only the
number of conditioning points changes. -/
open MeasureTheory Set Function
namespace BeatAvg.Five

noncomputable def degreeTerm (a : ℝ × ℝ → ℝ) (b : ℝ)
    (p : ℝ × (ℝ × (Fin 3 → ℝ))) : ℝ :=
  a (p.1, p.2.1) * (s4 p.1 p.2.2 / 4 - b)

theorem bm_degreeTerm {a : ℝ × ℝ → ℝ} (ha : BM a) (b : ℝ) : BM (degreeTerm a b) := by
  have hs : BM fun p : ℝ × (ℝ × (Fin 3 → ℝ)) => s4 p.1 p.2.2 := by
    exact BM.sum _ fun i _ => (BM.ind measurableSet_S4).comp
      (measurable_insertNth_comp i (by fun_prop) (by fun_prop))
  exact (ha.comp (by fun_prop)).mul ((hs.div_const 4).sub (BM.const b))

theorem inner_degreeTerm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ × ℝ → ℝ) (b z : ℝ) :
    ∫ p, degreeTerm a b (z,p) ∂(μ.prod (iid 3 μ)) =
      (∫ y, a (z,y) ∂μ) * (deg μ z-b) := by
  unfold degreeTerm
  rw [integral_prod_mul (fun y => a (z,y)) (fun w => s4 z w / 4 - b),
    integral_sub (((bm_s4_slice z).div_const 4).integrable _) (integrable_const _),
    integral_s4_div]
  simp

theorem averaged_weight_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ × ℝ → ℝ} (ha : BM a) {M : ℝ}
    (h0 : ∀ p, 0 ≤ a p) (hM : ∀ p, a p ≤ M) (z : ℝ) :
    0 ≤ ∫ y, a (z,y) ∂μ ∧ (∫ y, a (z,y) ∂μ) ≤ M := by
  constructor
  · exact integral_nonneg fun y => h0 (z,y)
  · have hh := integral_mono ((ha.comp measurable_prodMk_left).integrable μ)
      (integrable_const M) (fun y => hM (z,y))
    simpa using hh

theorem integral_degreeTerm_lower {μ : Measure ℝ} (hμ : IsLaw μ)
    {a : ℝ × ℝ → ℝ} (ha : BM a) {M b ε : ℝ}
    (ha0 : ∀ p, 0 ≤ a p) (haM : ∀ p, a p ≤ M)
    (hε0 : 0 < ε) (hε : ε ≤ 1/36) (hP : C-ε ≤ P μ) (hb : b ≤ C) :
    -(M*(8*Real.sqrt ε)) ≤ ∫ p, degreeTerm a b p ∂(μ.prod (μ.prod (iid 3 μ))) := by
  have := hμ.prob
  rw [integral_prod _ ((bm_degreeTerm ha b).integrable _)]
  simp only [inner_degreeTerm]
  have ha' : BM fun z => ∫ y, a (z,y) ∂μ :=
    BM.of_nonneg_le ha.meas.stronglyMeasurable.integral_prod_right'.measurable
      (fun z => (averaged_weight_bounds μ ha ha0 haM z).1)
      (fun z => (averaged_weight_bounds μ ha ha0 haM z).2)
  exact weighted_degree_near_optimal hμ ha'
    (fun z => (averaged_weight_bounds μ ha ha0 haM z).1)
    (fun z => (averaged_weight_bounds μ ha ha0 haM z).2) hε0 hε hP hb

def tailAll (q : ℝ) : Set (ℝ × (Fin 4 → ℝ)) := {p | ∀ i, p.2 i < q*p.1}
def tailWin (q : ℝ) : Set (ℝ × (Fin 4 → ℝ)) := {p | p.2 ∈ S4 ∧ ∀ i, p.2 i < q*p.1}

noncomputable def tailTerm (q x : ℝ) (p : ℝ × (Fin 4 → ℝ)) : ℝ :=
  x * ind (tailAll q) p - ind (tailWin q) p

theorem measurableSet_tailAll (q : ℝ) : MeasurableSet (tailAll q) := by
  have hh : tailAll q = ⋂ i, {p : ℝ × (Fin 4 → ℝ) | p.2 i < q*p.1} := by
    ext p; simp [tailAll]
  rw [hh]
  exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurableSet_tailWin (q : ℝ) : MeasurableSet (tailWin q) :=
  (measurable_snd measurableSet_S4).inter (measurableSet_tailAll q)

theorem bm_tailTerm (q x : ℝ) : BM (tailTerm q x) :=
  ((BM.ind (measurableSet_tailAll q)).const_mul x).sub (BM.ind (measurableSet_tailWin q))

theorem inner_tailTerm (μ : Measure ℝ) [IsProbabilityMeasure μ] (q x z : ℝ) :
    ∫ w, tailTerm q x (z,w) ∂(iid 4 μ) =
      x*(μ.real (Iio (q*z)))^4 - (iid 4 μ).real (S4 ∩ {w | ∀ i, w i < q*z}) := by
  unfold tailTerm
  rw [integral_sub ((((BM.ind (measurableSet_tailAll q)).const_mul x).comp
      measurable_prodMk_left).integrable _) (((BM.ind (measurableSet_tailWin q)).comp
      measurable_prodMk_left).integrable _), integral_const_mul,
    integral_ind_slice _ (measurableSet_tailAll q), integral_ind_slice _ (measurableSet_tailWin q)]
  change x*(iid 4 μ).real {w | ∀ i, w i < q*z} - _ = _
  rw [real_box]
  rfl

theorem integral_tailTerm_nonneg {μ : Measure ℝ} (hμ : IsLaw μ) (q : ℝ) :
    0 ≤ ∫ p, tailTerm q C p ∂(μ.prod (iid 4 μ)) := by
  have := hμ.prob
  rw [integral_prod _ ((bm_tailTerm q C).integrable _)]
  apply integral_nonneg
  intro z
  change 0 ≤ ∫ w, tailTerm q C (z,w) ∂(iid 4 μ)
  rw [inner_tailTerm]
  exact sub_nonneg.mpr (sublaw hμ (q*z))

end BeatAvg.Five
