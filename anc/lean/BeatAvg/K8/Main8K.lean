import BeatAvg.Main
import BeatAvg.Cert.CertValid
import BeatAvg.Cert.Static8
import BeatAvg.K8.EvalFSound
import BeatAvg.K8.Combine
import BeatAvg.K8.TbSpec

/-!
# `C ≤ B*` from kernel-checked facts

The finite facts are hypotheses here; they are proved by kernel evaluation in other modules.
-/

namespace BeatAvg.K8

open BeatAvg

theorem ordQ6_length : (ordQ 6).length = 15 := by decide

theorem ordQ8_len : (ordQ 8).length = 70 := by decide

theorem SG_restr {n : ℕ} {w : ℕ → ℝ} (hw : SG (n + 1) w) : SG n w :=
  ⟨fun i j hij hj => hw.mono i j hij (by omega), hw.nonneg,
    fun a b c d ha hb hc hd => hw.noTie a b c d (by omega) (by omega) (by omega) (by omega)⟩

/-- The kernel-checked facts used by the final theorem. -/
structure Facts : Prop where
  lev7 : LevelOk D.G7 40 6
  stat6 : statOk 6 = true
  all8 : ∀ T ∈ codes7, chk8 T = true
  tb : TbOk D.tb
  tf : TfOk D.tb D.tf D.quads D.masks
  reps : RepsOk
  encl : Fast.enclosureOk D.tb.encLo D.tb.encHi D.tb.encM = true

/-- Both inequalities for a sorted sample. -/
theorem sample_ok (hF : Facts) (hDn : 0 < Fast.tabs8.Dn) {ω : Fin 8 → ℝ} (hω : SG8 ω) :
    Lam (tabOf Fast.tabs8).D Bstar ω ≤ Bstar ∧
      Lam (tabOf Fast.tabs8).D (((100000 : ℤ) : ℝ) / ((100000 : ℤ) : ℝ)) ω
        ≤ (((100000 : ℤ) : ℝ) - ((1 : ℤ) : ℝ)) / ((100000 : ℤ) : ℝ) := by
  have hw : SG 8 (extN ω) := SG_extN hω
  have hT : code 7 (extN ω) ∈ codes7 := by
    have h := code_mem_allCodes hF.lev7 (SG_restr hw)
    rw [ordQ6_length] at h
    unfold codes7
    exact h
  have hx : ext 7 (extN ω) ∈ leavesT (code 7 (extN ω)) := by
    unfold leavesT
    exact exts_completeT hF.lev7 hF.stat6 hw
  have hl : leaf8 (code 7 (extN ω)) (ext 7 (extN ω)) = true := by
    have h := hF.all8 _ hT
    unfold chk8 at h
    exact List.all_eq_true.1 h _ hx
  unfold leaf8 at hl
  rw [Bool.or_eq_true] at hl
  rcases hl with h | h
  · rw [leafOkF_eq hF.tb hF.tf (extN ω)] at h
    exact leafOk_sound hF.tb hF.reps (enclosure_sound hF.encl) hDn (by norm_num) hω h
  · exfalso
    have hN : Nat.add (code 7 (extN ω)) (Nat.shiftLeft (ext 7 (extN ω)) 70) = code 8 (extN ω) := by
      rw [code8_split, nadd, nshl, Nat.shiftLeft_eq, show (2 : ℕ) ^ 70 = 4 ^ 35 by norm_num,
        mul_comm]
    rw [hN] at h
    unfold excl8 at h
    split at h
    · rename_i c _
      have := exclK_false hw c
      rw [ordQ8_len] at this
      rw [this] at h
      exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **`C ≤ B*` from the kernel-checked facts.** -/
theorem C_le_Bstar_of_facts (hF : Facts) : C ≤ Bstar := by
  have hs := static8
  have hvalid : (tabOf Fast.tabs8).D.Valid (Fast.cert8.B : ℝ) := cert_valid Fast.cert8 hs
  simp only [Fast.staticOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hDn⟩, -⟩, -⟩ := hs
  refine C_le_of_certificate hvalid (X := Bstar) (Cbar0 := 1) (δ := 1 / 100000) ?_ ?_ ?_ ?_
    C_le_one
  · norm_num
  · exact le_refl _
  · exact Lam_le_of_sorted _ _ _ fun ω hω => (sample_ok hF hDn hω).1
  · refine Lam_le_of_sorted _ _ _ fun ω hω => ?_
    have h := (sample_ok hF hDn hω).2
    norm_num at h ⊢
    exact h

end BeatAvg.K8
