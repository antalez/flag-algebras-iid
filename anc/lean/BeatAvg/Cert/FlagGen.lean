import BeatAvg.Bounded
import BeatAvg.Cert.Sort
import BeatAvg.Cert.CfgReal
import Fast.Gen

/-!
# A square (flag) family with `t` roots and `m` further points, in general form
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- Sorted roots followed by sorted further points. -/
noncomputable def ptsG {t m : ℕ} (p : (Fin t → ℝ) × (Fin m → ℝ)) : Fin (t + m) → ℝ :=
  Fast.appendF (sortT p.1) (sortT p.2)

theorem measurable_ptsG {t m : ℕ} : Measurable (ptsG (t := t) (m := m)) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i.val < t
  · have : Measurable fun p : (Fin t → ℝ) × (Fin m → ℝ) => sortT p.1 ⟨i.val, h⟩ :=
      (measurable_pi_apply _).comp (measurable_sortT.comp measurable_fst)
    simpa [ptsG, Fast.appendF, h] using this
  · have : Measurable fun p : (Fin t → ℝ) × (Fin m → ℝ) => sortT p.2 ⟨i.val - t, by omega⟩ :=
      (measurable_pi_apply _).comp (measurable_sortT.comp measurable_snd)
    simpa [ptsG, Fast.appendF, h] using this

theorem appendF_comp {α β : Type} {t m : ℕ} (g : α → β) (a : Fin t → α) (b : Fin m → α) :
    Fast.appendF (g ∘ a) (g ∘ b) = g ∘ Fast.appendF a b := by
  funext i
  simp only [Fast.appendF, comp_apply]
  split_ifs <;> rfl

/-- A family: index maps for the roots and the two groups of further points, a flag function of
the configuration, the number of flags, and a quadratic form. -/
structure Fam (n t m : ℕ) where
  eR : Fin t → Fin n
  eT : Fin m → Fin n
  eT' : Fin m → Fin n
  F : Fast.Cfg (t + m) → ℕ
  N : ℕ
  Q : ℕ → ℕ → ℝ

variable {n t m : ℕ}

/-- The index map of the three blocks. -/
def Fam.e (f : Fam n t m) : Fin t ⊕ (Fin m ⊕ Fin m) → Fin n :=
  Sum.elim f.eR (Sum.elim f.eT f.eT')

/-- The flag of roots and further points. -/
noncomputable def Fam.flag (f : Fam n t m) (p : (Fin t → ℝ) × (Fin m → ℝ)) : ℕ :=
  f.F (cfgOf (ptsG p)) % f.N

/-- The kernel on (roots, points, points). -/
noncomputable def Fam.K (f : Fam n t m) (p : (Fin t → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ))) : ℝ :=
  f.Q (f.flag (p.1, p.2.1)) (f.flag (p.1, p.2.2))

/-- The term of a sample. -/
noncomputable def Fam.term (f : Fam n t m) (v : Fin n → ℝ) : ℝ :=
  f.K (v ∘ f.eR, (v ∘ f.eT, v ∘ f.eT'))

theorem Fam.term_eq (f : Fam n t m) (v : Fin n → ℝ) : f.term v = f.K (split3 f.e v) := rfl

/-- Configurations are finitely many. -/
instance (k : ℕ) : Fintype (Fast.Cfg k) :=
  Fintype.ofEquiv ((Fin k → Fin k → Bool) × (Fin k → Fin k → Fin k → Fin k → Bool))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun c => (c.lt, c.sb)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The flags are bounded (no assumption on `N`). -/
theorem Fam.exists_flag_bound (f : Fam n t m) : ∃ M, ∀ p, f.flag p < M :=
  ⟨(Finset.univ.sup fun c : Fast.Cfg (t + m) => f.F c % f.N) + 1, fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun c : Fast.Cfg (t + m) => f.F c % f.N)
      (Finset.mem_univ (cfgOf (ptsG p))))⟩

theorem Fam.measurable_flag (f : Fam n t m) : Measurable f.flag :=
  (measurable_of_cfg fun c : Fast.Cfg (t + m) => f.F c % f.N).comp
    (measurable_cfgOf.comp measurable_ptsG)

/-- The set of (roots, points) with flag `i`. -/
def Fam.Fi (f : Fam n t m) (i : ℕ) : Set ((Fin t → ℝ) × (Fin m → ℝ)) := {q | f.flag q = i}

theorem Fam.measurableSet_Fi (f : Fam n t m) (i : ℕ) : MeasurableSet (f.Fi i) :=
  f.measurable_flag (measurableSet_singleton i)

theorem Fam.ind_Fi (f : Fam n t m) (i : ℕ) (q : (Fin t → ℝ) × (Fin m → ℝ)) :
    ind (f.Fi i) q = if f.flag q = i then 1 else 0 := by
  by_cases h : f.flag q = i
  · rw [ind_of_mem (show q ∈ f.Fi i from h), if_pos h]
  · rw [ind_of_notMem (show q ∉ f.Fi i from h), if_neg h]

theorem Fam.K_eq (f : Fam n t m) (M : ℕ) (hM : ∀ q, f.flag q < M)
    (p : (Fin t → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ))) :
    f.K p = ∑ i : Fin M, ∑ j : Fin M,
      ind (f.Fi i.val) (p.1, p.2.1) * f.Q i.val j.val * ind (f.Fi j.val) (p.1, p.2.2) := by
  simp only [Fam.ind_Fi, Fam.K]
  have h1 := hM (p.1, p.2.1)
  have h2 := hM (p.1, p.2.2)
  rw [Finset.sum_eq_single (⟨f.flag (p.1, p.2.1), h1⟩ : Fin M)]
  · rw [Finset.sum_eq_single (⟨f.flag (p.1, p.2.2), h2⟩ : Fin M)]
    · simp
    · intro j _ hj
      have : ¬ f.flag (p.1, p.2.2) = j.val := fun h => hj (Fin.ext h.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    have : ¬ f.flag (p.1, p.2.1) = i.val := fun h => hi (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Fam.bm_K (f : Fam n t m) : BM f.K := by
  obtain ⟨M, hM⟩ := f.exists_flag_bound
  have h : f.K = fun p => ∑ i : Fin M, ∑ j : Fin M,
      ind (f.Fi i.val) (p.1, p.2.1) * f.Q i.val j.val * ind (f.Fi j.val) (p.1, p.2.2) :=
    funext (f.K_eq M hM)
  rw [h]
  refine BM.sum _ fun i _ => BM.sum _ fun j _ => ?_
  have h1 : BM fun p : (Fin t → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ)) => ind (f.Fi i.val) (p.1, p.2.1) :=
    (BM.ind (f.measurableSet_Fi i.val)).comp (by fun_prop)
  have h2 : BM fun p : (Fin t → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ)) => ind (f.Fi j.val) (p.1, p.2.2) :=
    (BM.ind (f.measurableSet_Fi j.val)).comp (by fun_prop)
  exact (h1.mul (BM.const _)).mul h2

end BeatAvg
