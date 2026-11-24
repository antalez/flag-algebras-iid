import Fast.Cover
import Mathlib.Tactic

/-!
# Logical content of the level checks
-/

namespace BeatAvg

/-- Default stage. -/
abbrev dS : Fast.Stage := ⟨#[], #[], #[]⟩

/-- The properties of a level that the enumeration relies on. -/
structure LevelSpec (L : Fast.Level) (R : Array Fast.Pat) : Prop where
  stages_size : L.stages.size = L.n
  m_eq : L.m = (Fast.combos L.n).length
  src : ∀ pos < L.m, (L.src.getD pos (0, 0)).1 < L.stages.size ∧
    (L.src.getD pos (0, 0)).2 < (L.stages.getD (L.src.getD pos (0, 0)).1 dS).pm.size ∧
    (L.stages.getD (L.src.getD pos (0, 0)).1 dS).pm.getD (L.src.getD pos (0, 0)).2 0 = pos
  olds : ∀ s < L.stages.size, ∀ o ∈ (L.stages.getD s dS).olds.toList,
    o.2.1 < s ∧ o.1 < (L.stages.getD s dS).pm.size ∧
      o.2.2 < (L.stages.getD o.2.1 dS).pm.size ∧
      (L.stages.getD o.2.1 dS).pm.getD o.2.2 0 = (L.stages.getD s dS).pm.getD o.1 0
  pm : ∀ j < L.n, (L.stages.getD j dS).pm = Fast.pmOf L.n (L.n - 1 - j)
  buckets : ∀ s < L.stages.size, ∀ T ∈ R.toList,
    T ∈ ((L.stages.getD s dS).buckets.getD (Fast.keyT (L.stages.getD s dS) T) #[]).toList

theorem levelSpec_of {L : Fast.Level} {R : Array Fast.Pat} (h : Fast.levelOk L R = true) :
    LevelSpec L R := by
  simp only [Fast.levelOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · intro pos hpos
    have := List.all_eq_true.1 h4 pos (List.mem_range.2 hpos)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · intro s hs o ho
    have := List.all_eq_true.1 (List.all_eq_true.1 h5 s (List.mem_range.2 hs)) o ho
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · intro j hj
    have := List.all_eq_true.1 h6 j (List.mem_range.2 hj)
    simpa using this
  · intro s hs T hT
    have hb := List.all_eq_true.1 h7 s (List.mem_range.2 hs)
    change (if (L.stages.getD s dS).olds.isEmpty = true then
        (L.stages.getD s dS).buckets.getD 0 #[] == R
      else R.toList.all fun T =>
        ((L.stages.getD s dS).buckets.getD (Fast.keyT (L.stages.getD s dS) T) #[]).toList.contains T)
      = true at hb
    by_cases hempty : (L.stages.getD s dS).olds.isEmpty = true
    · rw [if_pos hempty] at hb
      have hR : (L.stages.getD s dS).buckets.getD 0 #[] = R := eq_of_beq hb
      have hkey : Fast.keyT (L.stages.getD s dS) T = 0 := by
        unfold Fast.keyT
        have : (L.stages.getD s dS).olds.toList = [] := by
          simpa [Array.isEmpty_iff] using hempty
        rw [this]; rfl
      rw [hkey, hR]; exact hT
    · rw [if_neg hempty] at hb
      have := List.all_eq_true.1 hb T hT
      exact List.contains_iff_mem.1 this

end BeatAvg
