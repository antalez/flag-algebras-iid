import BeatAvg.Cert.FamSum

/-!
# Reduction to sorted samples on `n` points
-/

open MeasureTheory Set Function Finset

namespace BeatAvg

variable {n : ℕ}

/-- A sorted sample of `n` points in general position. -/
structure SGn (n : ℕ) (ω : Fin n → ℝ) : Prop where
  mono : StrictMono ω
  nonneg : ∀ i, 0 ≤ ω i
  noTie : ∀ a b c d : Fin n, a ≠ d → b ≠ d → c ≠ d → ω a + ω b + ω c ≠ 2 * ω d

theorem LamF_comp_perm (e4 : Fin 4 → Fin n) (fams : List (PFam n)) (ω : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : LamF e4 fams (ω ∘ ⇑σ) = LamF e4 fams ω := by
  unfold LamF
  congr 1
  have h := Equiv.sum_comp (Equiv.mulLeft σ)
    (fun π : Equiv.Perm (Fin n) => lamF e4 fams (ω ∘ ⇑π))
  rw [← h]
  rfl

theorem exists_sortedN {ω : Fin n → ℝ} (hω : GenericN n ω) :
    ∃ σ : Equiv.Perm (Fin n), SGn n (ω ∘ ⇑σ) := by
  obtain ⟨hnn, hinj, htie⟩ := hω
  refine ⟨Tuple.sort ω, ?_, fun i => hnn _, ?_⟩
  · exact (Tuple.monotone_sort ω).strictMono_of_injective (hinj.comp (Tuple.sort ω).injective)
  · intro a b c d had hbd hcd
    exact htie _ _ _ _ ((Tuple.sort ω).injective.ne had) ((Tuple.sort ω).injective.ne hbd)
      ((Tuple.sort ω).injective.ne hcd)

theorem LamF_le_of_sorted (e4 : Fin 4 → Fin n) (fams : List (PFam n)) (y : ℝ)
    (h : ∀ ω, SGn n ω → LamF e4 fams ω ≤ y) : ∀ ω, GenericN n ω → LamF e4 fams ω ≤ y := by
  intro ω hω
  obtain ⟨σ, hσ⟩ := exists_sortedN hω
  rw [← LamF_comp_perm e4 fams ω σ]
  exact h _ hσ

/-- Extension of a sample to all natural indices. -/
noncomputable def extNn (ω : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then ω ⟨i, h⟩ else 0

theorem extNn_val (ω : Fin n → ℝ) (i : Fin n) : extNn ω i.val = ω i := by
  simp [extNn, i.isLt]

theorem SG_extNn (hn : 0 < n) {ω : Fin n → ℝ} (hω : SGn n ω) : SG n (extNn ω) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hj
    have hi : i < n := hij.trans hj
    have := hω.mono (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)
    simpa [extNn, hi, hj] using this
  · simpa [extNn, hn] using hω.nonneg ⟨0, hn⟩
  · intro a b c d ha hb hc hd had hbd hcd
    have := hω.noTie ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (by simpa using had) (by simpa using hbd)
      (by simpa using hcd)
    simpa [extNn, ha, hb, hc, hd] using this

/-- The configuration of a sorted sample in general position is that of its pattern. -/
theorem cfgOf_eq_patG (hn : 0 < n) {idx : ℕ → ℕ → ℕ → ℕ → ℕ} (hidx : IdxOk n idx)
    {ω : Fin n → ℝ} (hω : SGn n ω) :
    cfgOf ω = Fast.cfgOfPatG n idx (patArr n (extNn ω)) := by
  apply cfg_ext
  · intro i j
    simp only [cfgOf, Fast.cfgOfPatG]
    apply decide_eq_decide.2
    exact hω.mono.lt_iff_lt
  · intro a b c d
    simp only [cfgOf, Fast.cfgOfPatG]
    rw [sbPatG_spec hidx (SG_extNn hn hω) a.isLt b.isLt c.isLt d.isLt]
    apply decide_eq_decide.2
    simp only [extNn_val, ne_eq, Fin.val_inj]

end BeatAvg
