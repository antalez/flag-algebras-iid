import BeatAvg.Cert.Levels
import BeatAvg.Cert.CheckSound
import BeatAvg.Cert.CertValid
import BeatAvg.Main
import BeatAvg.Cert.Native8
import BeatAvg.Cert.Static8

/-!
# The order-8 certificate implies `C ≤ B*` (given the finite check and `C ≤ Cbar0`)
-/

namespace BeatAvg

theorem R5_complete {w : ℕ → ℝ} (hw : SG 5 w) : patArr 5 w ∈ Fast.R5.toList :=
  level_complete (by norm_num) Fast.R4 Fast.fm cov5 (fun _ _ => base4) hw

theorem R6_complete {w : ℕ → ℝ} (hw : SG 6 w) : patArr 6 w ∈ Fast.R6.toList :=
  level_complete (by norm_num) Fast.R5 Fast.fm cov6 (fun _ h => R5_complete h) hw

theorem R7_complete {w : ℕ → ℝ} (hw : SG 7 w) : patArr 7 w ∈ Fast.R7.toList :=
  level_complete (by norm_num) Fast.R6 Fast.fm cov7 (fun _ h => R6_complete h) hw

/-- The parallel check says that no leaf of level 8 fails. -/
theorem go_empty_of_goPar {L : Fast.Level} {keep : Fast.Pat → Bool} (hn : L.n = 8)
    (h : Fast.goPar L keep = true) : Fast.go L keep 8 [] = [] := by
  unfold Fast.goPar at h
  rw [List.all_eq_true] at h
  show (Fast.cands (L.stages.getD ([] : List Fast.Pat).length dS) []).flatMap
    (fun T => Fast.go L keep 7 ([] ++ [T])) = []
  rw [List.flatMap_eq_nil_iff]
  intro T hT
  have h1 := h _ (List.mem_map_of_mem hT)
  have h2 : (Fast.go L keep (L.n - 1) [T]).isEmpty = true := h1
  rw [hn] at h2
  simpa using h2

/-- Every sorted sample in general position passes the leaf check. -/
theorem leaf_ok (hmain : Fast.goPar Fast.L8 (fun P => !Fast.leafOk P) = true) {w : ℕ → ℝ}
    (hw : SG 8 w) : Fast.leafOk (patArr 8 w) = true := by
  by_contra hne
  have hL : LevelSpec Fast.L8 Fast.R7 := levelSpec_mkLevel Fast.R7 cov8
  have ht := target_of (n := 8) (by norm_num) hL rfl (fun _ h => R7_complete h) hw
  have hmem := go_complete hL ht (fun P => !Fast.leafOk P) (by simpa using hne) 8 0 []
    (by show 0 + 8 = 8; rfl) ⟨rfl, fun j hj => by omega⟩
  have hempty := go_empty_of_goPar (L := Fast.L8) rfl hmain
  have : patArr 8 w ∈ Fast.go Fast.L8 (fun P => !Fast.leafOk P) 8 [] := hmem
  rw [hempty] at this
  simp at this

end BeatAvg

namespace BeatAvg

theorem checkBoth_eq (lo hi : ℤ) (m : ℕ) (t : Fast.Tabs) (p q e : ℤ) (c : Fast.Cfg 8) :
    Fast.checkBoth lo hi m t p q e c
      = (Fast.checkB lo hi m t c && Fast.checkC lo hi m t p q e c) := rfl

theorem checks_of_main (hmain : Fast.goPar Fast.L8 (fun P => !Fast.leafOk P) = true)
    {ω : Fin 8 → ℝ} (hω : SG8 ω) :
    Fast.checkB Fast.cert8.encLo Fast.cert8.encHi Fast.cert8.encM Fast.tabs8 (cfgOf ω) = true ∧
    Fast.checkC Fast.cert8.encLo Fast.cert8.encHi Fast.cert8.encM Fast.tabs8 100000 100000
      Fast.cbarE (cfgOf ω) = true := by
  have hw := SG_extN hω
  have h := leaf_ok hmain hw
  unfold Fast.leafOk at h
  rw [show Fast.combos8 = Fast.combos 8 from rfl, excl_false hw, Bool.or_false,
    ← cfgOf_eq_pat hω, checkBoth_eq, Bool.and_eq_true] at h
  exact h

/-- **Order 8.** If the finite check passes, then `C ≤ B*`. The second point of the two-point
criterion is `Cbar0 = 1`, so the only prior bound used is `C ≤ 1`. -/
theorem C_le_Bstar_of_check (hmain : Fast.goPar Fast.L8 (fun P => !Fast.leafOk P) = true) :
    C ≤ Bstar := by
  have hs := static8
  have hvalid : (tabOf Fast.tabs8).D.Valid (Fast.cert8.B : ℝ) := cert_valid Fast.cert8 hs
  simp only [Fast.staticOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨henc, -⟩, -⟩, -⟩, -⟩, hDn⟩, -⟩, -⟩ := hs
  have he := enclosure_sound henc
  have hE : (Fast.cbarE : ℝ) = 1 := by simp [Fast.cbarE]
  refine C_le_of_certificate hvalid (X := Bstar) (Cbar0 := 1)
    (δ := 1 / 100000) ?_ ?_ ?_ ?_ C_le_one
  · norm_num
  · exact le_refl _
  · exact Lam_le_of_sorted _ _ _ fun ω hω =>
      checkB_sound he Fast.tabs8 hDn hω (checks_of_main hmain hω).1
  · refine Lam_le_of_sorted _ _ _ fun ω hω => ?_
    have h := checkC_sound he Fast.tabs8 hDn (p := 100000) (q := 100000) (by norm_num) hω
      (checks_of_main hmain hω).2
    rw [hE] at h
    push_cast at h
    rw [sub_div, div_self (by norm_num : (100000 : ℝ) ≠ 0)] at h
    exact h

end BeatAvg
