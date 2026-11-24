import BeatAvg.Four.Config
import BeatAvg.Cert.FlagGen

/-! Colored flag families with arbitrary numbers of roots and extensions.
The conditional-independence proof is the same as for additive flags. -/
open MeasureTheory Set Function
namespace BeatAvg.Four

/-- A family: index maps for the roots and the two groups of further points, a flag function of
the configuration, the number of flags, and a quadratic form. -/
structure Fam (n t m : ℕ) where
  eR : Fin t → Fin n
  eT : Fin m → Fin n
  eT' : Fin m → Fin n
  F : Config (t + m) → ℕ
  N : ℕ
  Q : ℕ → ℕ → ℝ

variable {n t m : ℕ}

/-- The index map of the three blocks. -/
def Fam.e (f : Fam n t m) : Fin t ⊕ (Fin m ⊕ Fin m) → Fin n :=
  Sum.elim f.eR (Sum.elim f.eT f.eT')

/-- The flag of roots and further points. -/
noncomputable def Fam.flag (f : Fam n t m) (p : (Fin t → ℝ) × (Fin m → ℝ)) : ℕ :=
  f.F (configOf (ptsG p)) % f.N

/-- The kernel on (roots, points, points). -/
noncomputable def Fam.K (f : Fam n t m) (p : (Fin t → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ))) : ℝ :=
  f.Q (f.flag (p.1, p.2.1)) (f.flag (p.1, p.2.2))

/-- The term of a sample. -/
noncomputable def Fam.term (f : Fam n t m) (v : Fin n → ℝ) : ℝ :=
  f.K (v ∘ f.eR, (v ∘ f.eT, v ∘ f.eT'))

theorem Fam.term_eq (f : Fam n t m) (v : Fin n → ℝ) : f.term v = f.K (split3 f.e v) := rfl

/-- Configurations are finitely many. -/
noncomputable instance (k : ℕ) : Fintype (Config k) := Fintype.ofFinite _

/-- The flags are bounded (no assumption on `N`). -/
theorem Fam.exists_flag_bound (f : Fam n t m) : ∃ M, ∀ p, f.flag p < M :=
  ⟨(Finset.univ.sup fun c : Config (t + m) => f.F c % f.N) + 1, fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun c : Config (t + m) => f.F c % f.N)
      (Finset.mem_univ (configOf (ptsG p))))⟩

theorem Fam.measurable_flag (f : Fam n t m) : Measurable f.flag :=
  (measurable_of_config fun c : Config (t + m) => f.F c % f.N).comp
    (measurable_configOf.comp measurable_ptsG)

/-- The set of (roots, points) with flag `i`. -/
def Fam.Fi (f : Fam n t m) (i : ℕ) : Set ((Fin t → ℝ) × (Fin m → ℝ)) := {q | f.flag q = i}

theorem Fam.measurableSet_Fi (f : Fam n t m) (i : ℕ) : MeasurableSet (f.Fi i) :=
  f.measurable_flag (measurableSet_singleton i)

theorem Fam.ind_Fi (f : Fam n t m) (i : ℕ) (q : (Fin t → ℝ) × (Fin m → ℝ)) :
    ind (f.Fi i) q = if f.flag q = i then 1 else 0 := by
  by_cases h : f.flag q = i
  · rw [ind_of_mem (show q ∈ f.Fi i from h), ite_eq_left h]
  · rw [ind_of_notMem (show q ∉ f.Fi i from h), ite_eq_right h]

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

end BeatAvg.Four
