import BeatAvg.Cert.Assemble
import BeatAvg.Cert.PatSb

/-!
# Reduction to sorted samples, and the configuration of a sorted sample from its pattern
-/

open MeasureTheory Set Function

namespace BeatAvg

variable {nΦ : ℕ} {Θ : Type} [Fintype Θ]

theorem Lam_comp_perm (D : CertData nΦ Θ) (x : ℝ) (ω : Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) :
    Lam D x (ω ∘ ⇑σ) = Lam D x ω := by
  unfold Lam
  congr 1
  have h := Equiv.sum_comp (Equiv.mulLeft σ) (fun π : Equiv.Perm (Fin 8) => lam D x (ω ∘ ⇑π))
  rw [← h]
  rfl

theorem exists_sorted {ω : Fin 8 → ℝ} (hω : Generic ω) :
    ∃ σ : Equiv.Perm (Fin 8), SG8 (ω ∘ ⇑σ) := by
  obtain ⟨hnn, hinj, htie⟩ := hω
  refine ⟨Tuple.sort ω, ?_, hnn _, ?_⟩
  · exact (Tuple.monotone_sort ω).strictMono_of_injective (hinj.comp (Tuple.sort ω).injective)
  · intro a b c d had hbd hcd
    exact htie _ _ _ _ ((Tuple.sort ω).injective.ne had) ((Tuple.sort ω).injective.ne hbd)
      ((Tuple.sort ω).injective.ne hcd)

/-- It suffices to bound the functional on sorted samples. -/
theorem Lam_le_of_sorted (D : CertData nΦ Θ) (x y : ℝ) (h : ∀ ω, SG8 ω → Lam D x ω ≤ y) :
    ∀ ω, Generic ω → Lam D x ω ≤ y := by
  intro ω hω
  obtain ⟨σ, hσ⟩ := exists_sorted hω
  rw [← Lam_comp_perm D x ω σ]
  exact h _ hσ

/-- Extension of a sample to all natural indices. -/
noncomputable def extN (ω : Fin 8 → ℝ) : ℕ → ℝ := fun i => if h : i < 8 then ω ⟨i, h⟩ else 0

theorem extN_val (ω : Fin 8 → ℝ) (i : Fin 8) : extN ω i.val = ω i := by
  simp [extN, i.isLt]

theorem SG_extN {ω : Fin 8 → ℝ} (hω : SG8 ω) : SG 8 (extN ω) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hj
    have hi : i < 8 := hij.trans hj
    have := hω.mono (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)
    simpa [extN, hi, hj] using this
  · simpa [extN] using hω.nonneg
  · intro a b c d ha hb hc hd had hbd hcd
    have := hω.noTie ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (by simpa using had) (by simpa using hbd)
      (by simpa using hcd)
    simpa [extN, ha, hb, hc, hd] using this

/-- The configuration of a sorted sample in general position is that of its pattern. -/
theorem cfgOf_eq_pat {ω : Fin 8 → ℝ} (hω : SG8 ω) :
    cfgOf ω = Fast.cfgOfPat (patArr 8 (extN ω)) := by
  apply cfg_ext
  · intro i j
    simp only [cfgOf, Fast.cfgOfPat]
    apply decide_eq_decide.2
    exact hω.mono.lt_iff_lt
  · intro a b c d
    simp only [cfgOf, Fast.cfgOfPat]
    rw [sbPat_spec (SG_extN hω) a.isLt b.isLt c.isLt d.isLt]
    apply decide_eq_decide.2
    simp only [extN_val, ne_eq, Fin.val_inj]

end BeatAvg
