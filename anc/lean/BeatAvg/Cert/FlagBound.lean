import BeatAvg.Cert.FlagGen2
import BeatAvg.Atomless

/-!
# The flag bound in sample form

For a list of square families on `n` points: if the symmetrised functional `objective + squares`
is at most `lam` on every sample in general position, then `C ≤ lam`.
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- General position for `n` sample points. -/
def GenericN (n : ℕ) (ω : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ ω i) ∧ Function.Injective ω ∧
    ∀ a b c d : Fin n, a ≠ d → b ≠ d → c ≠ d → ω a + ω b + ω c ≠ 2 * ω d

theorem ae_genericN {n : ℕ} {μ : Measure ℝ} (hμ : IsLaw μ) [NullSingletonClass μ] :
    ∀ᵐ ω ∂(iid n μ), GenericN n ω := by
  have := hμ.prob
  have h1 := iid_nonneg_ae (n := n) hμ
  have h2 : ∀ᵐ ω ∂(iid n μ), ∀ i j : Fin n, i ≠ j → ω i ≠ ω j := by
    simp only [ae_all_iff]
    intro i j hij
    have h := pi_graph_null (ι := Fin n) μ i (fun ω => ω j) (measurable_pi_apply j)
      (fun ω y => by simp [Function.update_of_ne (Ne.symm hij)])
    rw [ae_iff]
    simpa using h
  have h3 : ∀ᵐ ω ∂(iid n μ), ∀ a b c d : Fin n, a ≠ d → b ≠ d → c ≠ d →
      ω a + ω b + ω c ≠ 2 * ω d := by
    simp only [ae_all_iff]
    intro a b c d had hbd hcd
    have h := pi_graph_null (ι := Fin n) μ d (fun ω => (ω a + ω b + ω c) / 2) (by fun_prop)
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

/-- A family with its numbers of roots and further points. -/
structure PFam (n : ℕ) where
  t : ℕ
  m : ℕ
  fam : Fam n t m

/-- Conditions under which a family has nonnegative mean. -/
structure PFam.Good {n : ℕ} (f : PFam n) : Prop where
  inj : Injective f.fam.e
  psd : ∀ (M : ℕ) (u : Fin M → ℝ), 0 ≤ ∑ i, ∑ j, u i * f.fam.Q i.val j.val * u j

/-- Objective term: the four points at positions `e4` succeed (target last). -/
noncomputable def objG {n : ℕ} (e4 : Fin 4 → Fin n) (v : Fin n → ℝ) : ℝ := ind S4 (v ∘ e4)

/-- Objective plus the square terms. -/
noncomputable def lamF {n : ℕ} (e4 : Fin 4 → Fin n) (fams : List (PFam n)) (v : Fin n → ℝ) : ℝ :=
  objG e4 v + (fams.map fun f => f.fam.term v).sum

/-- The symmetrised functional. -/
noncomputable def LamF {n : ℕ} (e4 : Fin 4 → Fin n) (fams : List (PFam n)) (v : Fin n → ℝ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) * ∑ π : Equiv.Perm (Fin n), lamF e4 fams (v ∘ ⇑π)

theorem bm_term {n : ℕ} (f : PFam n) : BM f.fam.term := by
  have hm : Measurable (split3 (X := ℝ) f.fam.e) := by unfold split3; fun_prop
  exact f.fam.bm_K.comp hm

theorem squares_bm_nonneg {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (fams : List (PFam n))
    (hg : ∀ f ∈ fams, f.Good) :
    BM (fun v : Fin n → ℝ => (fams.map fun f => f.fam.term v).sum) ∧
      0 ≤ ∫ v, (fams.map fun f => f.fam.term v).sum ∂(iid n μ) := by
  induction fams with
  | nil => exact ⟨by simpa using BM.const (α := Fin n → ℝ) 0, by simp⟩
  | cons f l ih =>
    obtain ⟨hbm, hnn⟩ := ih fun g hgl => hg g (List.mem_cons_of_mem _ hgl)
    have hf := hg f List.mem_cons_self
    have hbf := bm_term f
    refine ⟨by simpa using hbf.add hbm, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hbf.integrable _) (hbm.integrable _)]
    have := f.fam.integral_term_nonneg hf.inj hf.psd μ
    exact add_nonneg this hnn

end BeatAvg

namespace BeatAvg

open MeasureTheory Set Function

/-- **The flag bound (sample form).** -/
theorem flag_bound {n : ℕ} (e4 : Fin 4 → Fin n) (he4 : Injective e4) (fams : List (PFam n))
    (hg : ∀ f ∈ fams, f.Good) (lam : ℝ) (h : ∀ ω, GenericN n ω → LamF e4 fams ω ≤ lam) :
    C ≤ lam := by
  have key : ∀ ν : Measure ℝ, IsLaw ν → NullSingletonClass ν → P ν ≤ lam := by
    intro ν hν hna
    have := hν.prob
    obtain ⟨hbm, hnn⟩ := squares_bm_nonneg ν fams hg
    have hme : Measurable fun v : Fin n → ℝ => v ∘ e4 :=
      Measurable.of_eval fun k => measurable_pi_apply (e4 k)
    have hbo : BM (objG e4) := (BM.ind measurableSet_S4).comp hme
    have hobj : ∫ v, objG e4 v ∂(iid n ν) = P ν := by
      have hmp := measurePreserving_comp_injective (ι := Fin n) ν e4 he4
      unfold objG
      rw [integral_comp_mp hmp (measurable_ind measurableSet_S4), integral_ind _ measurableSet_S4]
      rfl
    have hbl : BM (lamF e4 fams) := hbo.add hbm
    have hlam : P ν ≤ ∫ v, lamF e4 fams v ∂(iid n ν) := by
      unfold lamF
      rw [integral_add (hbo.integrable _) (hbm.integrable _), hobj]
      linarith
    have hperm : ∀ π : Equiv.Perm (Fin n),
        ∫ v : Fin n → ℝ, lamF e4 fams (v ∘ ⇑π) ∂(iid n ν) = ∫ v, lamF e4 fams v ∂(iid n ν) :=
      fun π => integral_comp_mp (measurePreserving_comp_injective (ι := Fin n) ν π π.injective)
        hbl.meas
    have hmp : ∀ π : Equiv.Perm (Fin n), Measurable fun v : Fin n → ℝ => v ∘ ⇑π := fun π =>
      Measurable.of_eval fun k => measurable_pi_apply (π k)
    have hint : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
        Integrable (fun v : Fin n → ℝ => lamF e4 fams (v ∘ ⇑π)) (iid n ν) := fun π _ =>
      (hbl.comp (hmp π)).integrable _
    have hLam : ∫ v, LamF e4 fams v ∂(iid n ν) = ∫ v, lamF e4 fams v ∂(iid n ν) := by
      simp only [LamF]
      rw [integral_const_mul, integral_finsetSum _ hint]
      simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
      have : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    have hbL : BM (LamF e4 fams) := by
      show BM fun v => (1 / (Nat.factorial n : ℝ)) * ∑ π : Equiv.Perm (Fin n), lamF e4 fams (v ∘ ⇑π)
      exact (BM.sum _ fun π _ => hbl.comp (hmp π)).const_mul _
    have hle : ∫ v, LamF e4 fams v ∂(iid n ν) ≤ lam := by
      have h1 := integral_mono_ae (hbL.integrable (iid n ν)) (integrable_const lam)
        ((ae_genericN hν).mono fun ω hω => h ω hω)
      simpa using h1
    linarith
  by_contra hcon
  have hgt : lam < C := not_le.mp hcon
  obtain ⟨ν, hν, hna, hP⟩ := exists_atomless_law_gt (ε := C - lam) (by linarith)
  have := key ν hν hna
  linarith

end BeatAvg
