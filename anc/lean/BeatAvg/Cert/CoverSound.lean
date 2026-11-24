import BeatAvg.Cert.CoverSpec
import Mathlib.Data.List.GetD

/-!
# Completeness of the join enumeration
-/

namespace BeatAvg

/-- A target pattern `P` with its restrictions `restr j` (to the points other than `n - 1 - j`). -/
structure Target (L : Fast.Level) (R : Array Fast.Pat) (P : Fast.Pat) (restr : ℕ → Fast.Pat) :
    Prop where
  size : P.size = L.m
  mem : ∀ j < L.n, restr j ∈ R.toList
  entry : ∀ j < L.n, ∀ k < (L.stages.getD j dS).pm.size,
    (restr j).getD k 0 = P.getD ((L.stages.getD j dS).pm.getD k 0) 0

variable {L : Fast.Level} {R : Array Fast.Pat} {P : Fast.Pat} {restr : ℕ → Fast.Pat}

/-- The first `s` choices are the restrictions of the target. -/
def Inv (restr : ℕ → Fast.Pat) (s : ℕ) (chosen : List Fast.Pat) : Prop :=
  chosen.length = s ∧ ∀ j < s, chosen.getD j #[] = restr j

theorem old_match (hL : LevelSpec L R) (ht : Target L R P restr) {s : ℕ} (hs : s < L.n)
    {chosen : List Fast.Pat} (hinv : Inv restr s chosen) :
    ∀ o ∈ (L.stages.getD s dS).olds.toList,
      (restr s).getD o.1 0 = (chosen.getD o.2.1 #[]).getD o.2.2 0 := by
  intro o ho
  have hs' : s < L.stages.size := by rw [hL.stages_size]; exact hs
  obtain ⟨h1, h2, h3, h4⟩ := hL.olds s hs' o ho
  rw [hinv.2 _ h1, ht.entry s hs o.1 h2, ht.entry o.2.1 (lt_trans h1 hs) o.2.2 h3, h4]

theorem cand_mem (hL : LevelSpec L R) (ht : Target L R P restr) {s : ℕ} (hs : s < L.n)
    {chosen : List Fast.Pat} (hinv : Inv restr s chosen) :
    restr s ∈ Fast.cands (L.stages.getD s dS) chosen := by
  have hs' : s < L.stages.size := by rw [hL.stages_size]; exact hs
  have hm := old_match hL ht hs hinv
  have hkey : Fast.keyS (L.stages.getD s dS) chosen = Fast.keyT (L.stages.getD s dS) (restr s) := by
    unfold Fast.keyS Fast.keyT
    apply List.foldl_ext
    intro acc o ho
    rw [hm o ho]
  unfold Fast.cands
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [hkey]
    exact hL.buckets s hs' _ (ht.mem s hs)
  · unfold Fast.matchesOld
    rw [List.all_eq_true]
    intro o ho
    rw [beq_iff_eq]
    exact hm o ho

theorem assemble_eq (hL : LevelSpec L R) (ht : Target L R P restr) {chosen : List Fast.Pat}
    (hinv : Inv restr L.n chosen) : Fast.assemble L chosen = P := by
  apply Array.ext
  · simp [Fast.assemble, ht.size]
  · intro i h1 h2
    have hi : i < L.m := by simpa [Fast.assemble] using h1
    obtain ⟨s1, s2, s3⟩ := hL.src i hi
    rw [hL.stages_size] at s1
    have e1 : (Fast.assemble L chosen)[i]
        = (chosen.getD (L.src.getD i (0, 0)).1 #[]).getD (L.src.getD i (0, 0)).2 0 := by
      simp [Fast.assemble]
    rw [e1, hinv.2 _ s1, ht.entry _ s1 _ s2, s3]
    simp [Array.getD, h2]

/-- The target pattern is among the leaves of the enumeration (if it is kept). -/
theorem go_complete (hL : LevelSpec L R) (ht : Target L R P restr) (keep : Fast.Pat → Bool)
    (hkeep : keep P = true) :
    ∀ (rem s : ℕ) (chosen : List Fast.Pat), s + rem = L.n → Inv restr s chosen →
      P ∈ Fast.go L keep rem chosen := by
  intro rem
  induction rem with
  | zero =>
    intro s chosen hsn hinv
    have hs : s = L.n := by omega
    subst hs
    simp only [Fast.go]
    rw [assemble_eq hL ht hinv, hkeep]
    simp
  | succ rem ih =>
    intro s chosen hsn hinv
    simp only [Fast.go]
    rw [List.mem_flatMap]
    refine ⟨restr s, ?_, ih (s + 1) (chosen ++ [restr s]) (by omega) ?_⟩
    · rw [hinv.1]
      exact cand_mem hL ht (by omega) hinv
    · refine ⟨by simp [hinv.1], ?_⟩
      intro j hj
      by_cases hjs : j < s
      · rw [List.getD_append _ _ _ _ (by rw [hinv.1]; exact hjs)]
        exact hinv.2 j hjs
      · have hjs' : j = s := by omega
        subst hjs'
        rw [List.getD_append_right _ _ _ _ (by rw [hinv.1])]
        simp [hinv.1]

end BeatAvg
