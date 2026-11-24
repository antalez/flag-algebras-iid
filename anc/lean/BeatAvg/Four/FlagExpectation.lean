import BeatAvg.Four.Flag

/-!
# A square family: nonnegative mean, invariance, evaluation on sorted samples
-/

open MeasureTheory Set Function

namespace BeatAvg.Four

variable {n t m : ℕ}

/-- The mean of a square term under an iid sample is nonnegative. -/
theorem Fam.integral_term_nonneg (f : Fam n t m) (he : Injective f.e)
    (hpsd : ∀ (M : ℕ) (u : Fin M → ℝ), 0 ≤ ∑ i, ∑ j, u i * f.Q i.val j.val * u j)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, f.term ω ∂(Measure.pi fun _ : Fin n => μ) := by
  obtain ⟨M, hM⟩ := f.exists_flag_bound
  have hmp := measurePreserving_split3 μ f.e he
  simp only [Fam.term_eq]
  rw [integral_comp_mp hmp f.bm_K.meas, integral_prod _ (f.bm_K.integrable _)]
  refine MeasureTheory.integral_nonneg fun r => ?_
  show 0 ≤ ∫ q, f.K (r, q) ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
  simp only [f.K_eq M hM]
  have hint : ∀ i j : Fin M, Integrable (fun q : (Fin m → ℝ) × (Fin m → ℝ) =>
      ind (f.Fi i.val) (r, q.1) * f.Q i.val j.val * ind (f.Fi j.val) (r, q.2))
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) := by
    intro i j
    have h1 : BM fun q : (Fin m → ℝ) × (Fin m → ℝ) => ind (f.Fi i.val) (r, q.1) :=
      (BM.ind (f.measurableSet_Fi i.val)).comp (by fun_prop)
    have h2 : BM fun q : (Fin m → ℝ) × (Fin m → ℝ) => ind (f.Fi j.val) (r, q.2) :=
      (BM.ind (f.measurableSet_Fi j.val)).comp (by fun_prop)
    exact ((h1.mul (BM.const _)).mul h2).integrable _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have hterm : ∀ i j : Fin M, ∫ q, ind (f.Fi i.val) (r, q.1) * f.Q i.val j.val
      * ind (f.Fi j.val) (r, q.2) ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
      = (∫ x, ind (f.Fi i.val) (r, x) ∂(Measure.pi fun _ : Fin m => μ)) * f.Q i.val j.val *
        (∫ x, ind (f.Fi j.val) (r, x) ∂(Measure.pi fun _ : Fin m => μ)) := by
    intro i j
    rw [integral_prod_mul (fun x => ind (f.Fi i.val) (r, x) * f.Q i.val j.val)
      (fun x => ind (f.Fi j.val) (r, x)), integral_mul_const]
  have hsum : ∀ i : Fin M, ∫ q, ∑ j : Fin M, ind (f.Fi i.val) (r, q.1) * f.Q i.val j.val
      * ind (f.Fi j.val) (r, q.2) ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
      = ∑ j : Fin M, (∫ x, ind (f.Fi i.val) (r, x) ∂(Measure.pi fun _ : Fin m => μ))
        * f.Q i.val j.val * (∫ x, ind (f.Fi j.val) (r, x) ∂(Measure.pi fun _ : Fin m => μ)) := by
    intro i
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  simp only [hsum]
  exact hpsd M fun i => ∫ x, ind (f.Fi i.val) (r, x) ∂(Measure.pi fun _ : Fin m => μ)

/-- Two arrangements agree up to permutations inside the three blocks. -/
def Fam.Rel (f : Fam n t m) (ρ ρ' : Fin n → Fin n) : Prop :=
  (∃ a : Equiv.Perm (Fin t), ∀ i, ρ (f.eR i) = ρ' (f.eR (a i))) ∧
    (∃ b : Equiv.Perm (Fin m), ∀ i, ρ (f.eT i) = ρ' (f.eT (b i))) ∧
    ∃ c : Equiv.Perm (Fin m), ∀ i, ρ (f.eT' i) = ρ' (f.eT' (c i))

instance (f : Fam n t m) (ρ ρ' : Fin n → Fin n) : Decidable (f.Rel ρ ρ') := by
  unfold Fam.Rel; infer_instance

theorem sortT_congr_perm {k : ℕ} (ω : Fin n → ℝ) (e : Fin k → Fin n) {ρ ρ' : Fin n → Fin n}
    (a : Equiv.Perm (Fin k)) (h : ∀ i, ρ (e i) = ρ' (e (a i))) :
    sortT ((ω ∘ ρ) ∘ e) = sortT ((ω ∘ ρ') ∘ e) := by
  have : (ω ∘ ρ) ∘ e = ((ω ∘ ρ') ∘ e) ∘ a := by
    funext i; simp only [comp_apply]; rw [h]
  rw [this, sortT_comp_perm]

theorem Fam.term_congr (f : Fam n t m) (ω : Fin n → ℝ) {ρ ρ' : Fin n → Fin n} (h : f.Rel ρ ρ') :
    f.term (ω ∘ ρ) = f.term (ω ∘ ρ') := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, c, hc⟩ := h
  have hR := sortT_congr_perm ω f.eR a ha
  have hT := sortT_congr_perm ω f.eT b hb
  have hT' := sortT_congr_perm ω f.eT' c hc
  simp only [Fam.term, Fam.K, Fam.flag, ptsG, hR, hT, hT']

/-- The term on a sorted sample, for an arrangement with sorted blocks. -/
theorem Fam.term_eval (f : Fam n t m) {ω : Fin n → ℝ} (hω : Monotone ω) {ρ : Fin n → Fin n}
    (h1 : Injective (ρ ∘ Fast.appendF f.eR f.eT)) (h2 : Injective (ρ ∘ Fast.appendF f.eR f.eT'))
    (hR : Monotone (ρ ∘ f.eR)) (hT : Monotone (ρ ∘ f.eT)) (hT' : Monotone (ρ ∘ f.eT')) :
    f.term (ω ∘ ρ) = f.Q (f.F ((configOf ω).comap (ρ ∘ Fast.appendF f.eR f.eT)) % f.N)
      (f.F ((configOf ω).comap (ρ ∘ Fast.appendF f.eR f.eT')) % f.N) := by
  have sR : sortT ((ω ∘ ρ) ∘ f.eR) = (ω ∘ ρ) ∘ f.eR := sortT_of_monotone (hω.comp hR)
  have sT : sortT ((ω ∘ ρ) ∘ f.eT) = (ω ∘ ρ) ∘ f.eT := sortT_of_monotone (hω.comp hT)
  have sT' : sortT ((ω ∘ ρ) ∘ f.eT') = (ω ∘ ρ) ∘ f.eT' := sortT_of_monotone (hω.comp hT')
  have p1 : ptsG ((ω ∘ ρ) ∘ f.eR, (ω ∘ ρ) ∘ f.eT) = ω ∘ (ρ ∘ Fast.appendF f.eR f.eT) := by
    unfold ptsG
    simp only [sR, sT]
    rw [appendF_comp (ω ∘ ρ) f.eR f.eT]
    rfl
  have p2 : ptsG ((ω ∘ ρ) ∘ f.eR, (ω ∘ ρ) ∘ f.eT') = ω ∘ (ρ ∘ Fast.appendF f.eR f.eT') := by
    unfold ptsG
    simp only [sR, sT']
    rw [appendF_comp (ω ∘ ρ) f.eR f.eT']
    rfl
  simp only [Fam.term, Fam.K, Fam.flag]
  rw [p1, p2, configOf_comp ω _ h1, configOf_comp ω _ h2]

end BeatAvg.Four
