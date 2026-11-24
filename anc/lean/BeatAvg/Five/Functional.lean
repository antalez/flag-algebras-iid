import BeatAvg.Five.Sample

/-! The five-point functional, its expectation bound, and symmetrization. -/
open MeasureTheory Set Function Finset
namespace BeatAvg.Five
open Fast.Five

theorem Fam.bm_term {n t m : ℕ} (f : Fam n t m) : BM f.term :=
  f.bm_K.comp (by fun_prop)

noncomputable def familyTerms : Fin 6 → (Fin 5 → ℝ) → ℝ :=
  ![(singletonFamily Data.block0).term, (tripleFamily Data.block1).term,
    (tripleFamily Data.block2).term, (tripleFamily Data.block3).term,
    (tripleFamily Data.block4).term, (tripleFamily Data.block5).term]

noncomputable def squares (ω : Fin 5 → ℝ) : ℝ := ∑ i, familyTerms i ω

theorem bm_squares : BM squares := by
  apply BM.sum
  intro i _
  fin_cases i <;> exact Fam.bm_term _

theorem integral_squares_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, squares ω ∂(iid 5 μ) := by
  have hi : ∀ i : Fin 6, Integrable (familyTerms i) (iid 5 μ) := by
    intro i; fin_cases i <;> exact (Fam.bm_term _).integrable _
  unfold squares
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply sum_nonneg
  intro i _
  fin_cases i
  · exact singleton_expectation μ
  · exact triple1_expectation μ
  · exact triple2_expectation μ
  · exact triple3_expectation μ
  · exact triple4_expectation μ
  · exact triple5_expectation μ

noncomputable def degreeSample (ω : Fin 5 → ℝ) : ℝ :=
  degreeTerm pairWeight Bstar (splitDegree ω)

noncomputable def tailSample (q x : ℝ) (ω : Fin 5 → ℝ) : ℝ := tailTerm q x (splitTail ω)

theorem bm_degreeSample : BM degreeSample :=
  (bm_degreeTerm bm_pairWeight Bstar).comp (by unfold splitDegree split3; fun_prop)

theorem bm_tailSample (q x : ℝ) : BM (tailSample q x) :=
  (bm_tailTerm q x).comp (by unfold splitTail split; fun_prop)

noncomputable def lam (x : ℝ) (ω : Fin 5 → ℝ) : ℝ :=
  objective ω + squares ω + degreeSample ω +
    (Data.wHalf : ℝ)*tailSample (1/2) x ω + (Data.wTwice : ℝ)*tailSample 2 x ω

theorem bm_lam (x : ℝ) : BM (lam x) :=
  (((bm_objective.add bm_squares).add bm_degreeSample).add
    ((bm_tailSample (1/2) x).const_mul _)).add ((bm_tailSample 2 x).const_mul _)

theorem integral_lam_lower {μ : Measure ℝ} (hμ : IsLaw μ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1/36) (hP : C-ε ≤ P μ) (hB : Bstar ≤ C) :
    C-ε-48*Real.sqrt ε ≤ ∫ ω, lam C ω ∂(iid 5 μ) := by
  have := hμ.prob
  have hsq := integral_squares_nonneg μ
  have hdeg := integral_sample_degree hμ hε0 hε hP hB
  have hhalf := integral_sample_tail hμ (1/2)
  have htwice := integral_sample_tail hμ 2
  change 0 ≤ ∫ ω, tailSample (1/2) C ω ∂(iid 5 μ) at hhalf
  change 0 ≤ ∫ ω, tailSample 2 C ω ∂(iid 5 μ) at htwice
  change -(48*Real.sqrt ε) ≤ ∫ ω, degreeSample ω ∂(iid 5 μ) at hdeg
  have hwH : (0 : ℝ) ≤ (Data.wHalf : ℝ) := by norm_num [Data.wHalf]
  have hwT : (0 : ℝ) ≤ (Data.wTwice : ℝ) := by norm_num [Data.wTwice]
  unfold lam
  rw [integral_add
    ((((bm_objective.add bm_squares).add bm_degreeSample).add
      ((bm_tailSample (1/2) C).const_mul _)).integrable _)
    (((bm_tailSample 2 C).const_mul _).integrable _)]
  rw [integral_add (((bm_objective.add bm_squares).add bm_degreeSample).integrable _)
    (((bm_tailSample (1/2) C).const_mul _).integrable _)]
  rw [integral_add ((bm_objective.add bm_squares).integrable _) (bm_degreeSample.integrable _),
    integral_add (bm_objective.integrable _) (bm_squares.integrable _),
    integral_objective, integral_const_mul, integral_const_mul]
  nlinarith [mul_nonneg hwH hhalf, mul_nonneg hwT htwice]

noncomputable def Lam (x : ℝ) (ω : Fin 5 → ℝ) : ℝ :=
  (1/120 : ℝ) * ∑ π : Equiv.Perm (Fin 5), lam x (ω ∘ π)

theorem bm_Lam (x : ℝ) : BM (Lam x) :=
  (BM.sum _ fun _ _ => (bm_lam x).comp (by fun_prop)).const_mul _

theorem integral_Lam (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ ω, Lam x ω ∂(iid 5 μ) = ∫ ω, lam x ω ∂(iid 5 μ) := by
  unfold Lam
  rw [integral_const_mul, integral_finsetSum _ (fun π _ =>
    ((bm_lam x).comp (by fun_prop)).integrable (iid 5 μ))]
  have hh : ∀ π : Equiv.Perm (Fin 5),
      (∫ ω, lam x (ω ∘ π) ∂(iid 5 μ)) = ∫ ω, lam x ω ∂(iid 5 μ) := by
    intro π
    exact integral_comp_mp (measurePreserving_comp_injective μ π π.injective) (bm_lam x).meas
  simp only [hh, sum_const, card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]
  ring

theorem Lam_affine (x y s : ℝ) (ω : Fin 5 → ℝ) :
    Lam ((1-s)*x+s*y) ω = (1-s)*Lam x ω+s*Lam y ω := by
  have hh : ∀ v, lam ((1-s)*x+s*y) v = (1-s)*lam x v+s*lam y v := by
    intro v
    unfold lam tailSample tailTerm
    ring
  simp only [Lam, hh, sum_add_distrib, ← mul_sum]
  ring

/-- Only the pointwise endpoint comparison remains to instantiate the old
probability argument with this concrete five-point functional. -/
theorem C_le_Bstar_of_endpoints
    (hb : ∀ ω, Generic ω → Lam Bstar ω ≤ Bstar)
    (h1 : ∀ ω, Generic ω → Lam 1 ω ≤ 1-9/10000) : C ≤ Bstar := by
  apply C_le_of_functional Lam (δ := 9/10000) (K := 48) (by norm_num) (by norm_num)
    bm_Lam Lam_affine hb h1
  intro μ hμ ε hε0 hε hP hB
  have := hμ.prob
  rw [integral_Lam]
  exact integral_lam_lower hμ hε0 hε hP hB

end BeatAvg.Five
