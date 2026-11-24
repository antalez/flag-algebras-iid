import BeatAvg.Cert.CoverSound
import BeatAvg.Cert.LevelProof
import BeatAvg.Cert.FarkasSound
import Mathlib.Data.List.GetD

/-!
# The pattern of a sorted sample is a leaf of the enumeration
-/

namespace BeatAvg

theorem skip_lt_skip (d : ℕ) {i j : ℕ} (h : i < j) : Fast.skip d i < Fast.skip d j := by
  unfold Fast.skip; split_ifs <;> omega

theorem skip_lt {n : ℕ} (d : ℕ) {i : ℕ} (h : i < n - 1) : Fast.skip d i < n := by
  unfold Fast.skip; split_ifs <;> omega

theorem skip_ne (d : ℕ) {i j : ℕ} (h : i ≠ j) : Fast.skip d i ≠ Fast.skip d j := by
  unfold Fast.skip; split_ifs <;> omega

/-- Deleting a point of a sorted sample in general position. -/
theorem SG_skip {n : ℕ} (hn : 2 ≤ n) {w : ℕ → ℝ} (hw : SG n w) (d : ℕ) :
    SG (n - 1) (w ∘ Fast.skip d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hj
    exact hw.mono _ _ (skip_lt_skip d hij) (skip_lt d hj)
  · exact hw.nonneg' (skip_lt d (by omega))
  · intro a b c e ha hb hc he hae hbe hce
    exact hw.noTie _ _ _ _ (skip_lt d ha) (skip_lt d hb) (skip_lt d hc) (skip_lt d he)
      (skip_ne d hae) (skip_ne d hbe) (skip_ne d hce)

theorem trit_skip (w : ℕ → ℝ) (d : ℕ) (q : ℕ × ℕ × ℕ × ℕ) :
    trit (w ∘ Fast.skip d) q = trit w (Fast.skipQ d q) := rfl

theorem skipQ_mem {n : ℕ} (hn : 1 ≤ n) (d : ℕ) {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Fast.combos (n - 1)) :
    Fast.skipQ d q ∈ Fast.combos n := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_combos.1 hq
  rw [mem_combos]
  exact ⟨skip_lt_skip d h1, skip_lt_skip d h2, skip_lt_skip d h3, skip_lt d h4⟩

theorem pmOf_size (n d : ℕ) : (Fast.pmOf n d).size = (Fast.combos (n - 1)).length := by
  simp [Fast.pmOf]

theorem pmOf_getD (n d : ℕ) {k : ℕ} (hk : k < (Fast.combos (n - 1)).length) :
    (Fast.pmOf n d).getD k 0
      = (Fast.combos n).idxOf (Fast.skipQ d ((Fast.combos (n - 1)).getD k (0, 0, 0, 0))) := by
  simp [Fast.pmOf, Fast.comboIdx, Array.getD, List.getD, hk]

theorem getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (a d : α) (h : a ∈ l) :
    l.getD (l.idxOf a) d = a := by
  have hi : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 h
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_idxOf hi

/-- An entry of the pattern of the sub-sample is the corresponding entry of the pattern. -/
theorem restr_entry {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ) (d : ℕ) {k : ℕ}
    (hk : k < (Fast.combos (n - 1)).length) :
    (patArr (n - 1) (w ∘ Fast.skip d)).getD k 0
      = (patArr n w).getD ((Fast.pmOf n d).getD k 0) 0 := by
  have hq := combos_getD hk
  have hq' := skipQ_mem hn d hq
  have hidx : (Fast.combos n).idxOf (Fast.skipQ d ((Fast.combos (n - 1)).getD k (0, 0, 0, 0)))
      < (Fast.combos n).length := List.idxOf_lt_length_iff.2 hq'
  rw [patArr_getD _ _ hk, trit_skip, pmOf_getD n d hk, patArr_getD _ _ hidx,
    getD_idxOf _ _ _ hq']

end BeatAvg

namespace BeatAvg

theorem target_of {n : ℕ} (hn : 2 ≤ n) {L : Fast.Level} {R : Array Fast.Pat} (hL : LevelSpec L R)
    (hLn : L.n = n) (hprev : ∀ w', SG (n - 1) w' → patArr (n - 1) w' ∈ R.toList) {w : ℕ → ℝ}
    (hw : SG n w) :
    Target L R (patArr n w) (fun j => patArr (n - 1) (w ∘ Fast.skip (n - 1 - j))) where
  size := by rw [patArr_size, hL.m_eq, hLn]
  mem := fun j _ => hprev _ (SG_skip hn hw _)
  entry := by
    intro j hj k hk
    have hpm := hL.pm j hj
    rw [hLn] at hpm
    rw [hpm] at hk ⊢
    rw [pmOf_size] at hk
    exact restr_entry (by omega) w _ hk

theorem excl_false {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) (fm : Std.HashMap (ℕ × ℕ) Fast.Cert) :
    Fast.excl fm (Fast.combos n) n (patArr n w) = false := by
  unfold Fast.excl
  split
  · rename_i cert _
    by_contra h
    exact farkas_sound hw cert (by simpa using h)
  · rfl

/-- The patterns of sorted samples on `n` points all appear at level `n`. -/
theorem level_complete {n : ℕ} (hn : 2 ≤ n) (R : Array Fast.Pat)
    (fm : Std.HashMap (ℕ × ℕ) Fast.Cert) (hcov : covOk n = true)
    (hprev : ∀ w', SG (n - 1) w' → patArr (n - 1) w' ∈ R.toList) {w : ℕ → ℝ} (hw : SG n w) :
    patArr n w ∈ (Fast.levelR fm n R).toList := by
  have hL := levelSpec_mkLevel R hcov
  have ht := target_of hn hL rfl hprev hw
  have h := go_complete hL ht (fun P => !Fast.excl fm (Fast.combos n) n P)
    (by simp [excl_false hw]) n 0 [] (by show 0 + n = n; omega) ⟨rfl, fun j hj => by omega⟩
  simpa [Fast.levelR] using h

theorem combos4 : Fast.combos 4 = [(0, 1, 2, 3)] := by decide

/-- Base case: the pattern of four points is a single trit. -/
theorem base4 {w : ℕ → ℝ} : patArr 4 w ∈ Fast.R4.toList := by
  unfold patArr
  rw [combos4]
  simp only [List.map_cons, List.map_nil, Fast.R4]
  unfold trit
  split_ifs <;> simp

end BeatAvg
