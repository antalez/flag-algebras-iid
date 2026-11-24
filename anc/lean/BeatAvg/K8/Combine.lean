import BeatAvg.K8.LevelK
import BeatAvg.K8.TrieSound
import BeatAvg.K8.Check8K

/-!
# Combining the pieces of the order-8 check
-/

namespace BeatAvg.K8

theorem nth_eq {α : Type} (d : α) : ∀ (l : List α) (n : ℕ), nth d l n = l.getD n d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth_eq d l n

theorem all_drop_take {α : Type} (p : α → Bool) (l : List α) {lo hi : ℕ} (h : lo ≤ hi)
    (h1 : ((l.drop lo).take (hi - lo)).all p = true) (h2 : (l.drop hi).all p = true) :
    (l.drop lo).all p = true := by
  have e : l.drop lo = (l.drop lo).take (hi - lo) ++ l.drop hi := by
    conv_lhs => rw [← List.take_append_drop (hi - lo) (l.drop lo)]
    rw [List.drop_drop]
    congr 2
    omega
  rw [e, List.all_append, h1, h2]
  rfl

theorem chkC_trans {g j lo hi : ℕ} (h1 : chkC g j lo hi = true) (h2 : chkCD g j hi = true)
    (h : lo ≤ hi) : chkCD g j lo = true := by
  unfold chkC chkCD at *
  have e : (candsJ D.G7 40 7 (T7 g j) 0).drop lo
      = ((candsJ D.G7 40 7 (T7 g j) 0).drop lo).take (hi - lo)
        ++ (candsJ D.G7 40 7 (T7 g j) 0).drop hi := by
    conv_lhs => rw [← List.take_append_drop (hi - lo) ((candsJ D.G7 40 7 (T7 g j) 0).drop lo)]
    rw [List.drop_drop]
    congr 2
    omega
  rw [e, joinFromT_append, List.all_append, h1, h2]
  rfl

theorem chkCD_zero {g j : ℕ} (h : chkCD g j 0 = true) : chkD g j 0 = true := by
  unfold chkCD at h
  unfold chkD
  rw [List.drop_zero] at h ⊢
  exact h

theorem chkT_trans {g j lo hi : ℕ} (h1 : chkT g j lo hi = true) (h2 : chkD g j hi = true)
    (h : lo ≤ hi) : chkD g j lo = true :=
  all_drop_take _ _ h h1 h2

theorem range'_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
  have : c - a = (b - a) + (c - b) := by omega
  rw [this, ← List.range'_append_1]
  congr 2
  omega

theorem chkJ_trans {g a b c : ℕ} (h1 : chkJ g a b = true) (h2 : chkJ g b c = true) (hab : a ≤ b)
    (hbc : b ≤ c) : chkJ g a c = true := by
  unfold chkJ at *
  rw [range'_split a b c hab hbc, List.all_append, h1, h2]
  rfl

theorem chkJ_one {g j : ℕ} (h : chkD g j 0 = true) : chkJ g j (j + 1) = true := by
  simp [chkJ, h]

theorem chkG_of {g n : ℕ} (h : chkJ g 0 n = true) (hn : (grp g).2.1 = n) : chkG g = true := by
  rw [chkG, hn]; exact h

theorem chkGs_trans {a b c : ℕ} (h1 : chkGs a b = true) (h2 : chkGs b c = true) (hab : a ≤ b)
    (hbc : b ≤ c) : chkGs a c = true := by
  unfold chkGs at *
  rw [range'_split a b c hab hbc, List.all_append, h1, h2]
  rfl

theorem chkGs_one {g : ℕ} (h : chkG g = true) : chkGs g (g + 1) = true := by
  simp [chkGs, h]

theorem unpackE_length (w : ℕ) : ∀ (c x : ℕ), (unpackE w c x).length = c
  | 0, _ => rfl
  | c + 1, x => by rw [unpackE, List.length_cons, unpackE_length w c]

theorem mem_allCodes_iff {sh wb T : ℕ} : ∀ {G : Grouped}, T ∈ allCodes sh wb G →
    ∃ g ∈ G, ∃ e ∈ unpackE wb g.2.1 g.2.2, T = Nat.add g.1 (Nat.shiftLeft e sh)
  | [], h => by simp [allCodes] at h
  | g :: G, h => by
    rw [allCodes, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      exact ⟨g, List.mem_cons_self, e, he, rfl⟩
    · obtain ⟨g', hg', e, he, rfl⟩ := mem_allCodes_iff h
      exact ⟨g', List.mem_cons_of_mem _ hg', e, he, rfl⟩

/-- **All the pieces give the check for every pattern of seven points.** (No `rfl` patterns
here: they make the elaborator evaluate the level data.) -/
theorem chk8_all {n : ℕ} (h : chkGs 0 n = true) (hn : D.G7.length = n) :
    ∀ T ∈ codes7, chk8 T = true := by
  intro T hT
  have hT' : T ∈ allCodes 30 40 D.G7 := by unfold codes7 at hT; exact hT
  obtain ⟨g, hg, e, he, hTe⟩ := mem_allCodes_iff (sh := 30) (wb := 40) (G := D.G7) hT'
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  obtain ⟨j, hj, hej⟩ := List.getElem_of_mem he
  have hG : chkG i = true := by
    unfold chkGs at h
    exact List.all_eq_true.1 h i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  have hgrp : grp i = g := by
    rw [grp, nth_eq, List.getD_eq_getElem _ _ hi, hgi]
  rw [unpackE_length] at hj
  unfold chkG chkJ at hG
  rw [hgrp] at hG
  have hD := List.all_eq_true.1 hG j (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  have h1 : nth 0 (unpackE 40 g.2.1 g.2.2) j = e := by
    rw [nth_eq, List.getD_eq_getElem _ _ (by rw [unpackE_length]; exact hj)]
    exact hej
  have hT7 : T7 i j = T := by
    unfold T7
    rw [hgrp, h1]
    exact hTe.symm
  rw [chkD, List.drop_zero, hT7] at hD
  exact hD

end BeatAvg.K8

namespace BeatAvg.K8

theorem rall_trans {p : ℕ → Bool} {a b c : ℕ} (h1 : (List.range' a (b - a)).all p = true)
    (h2 : (List.range' b (c - b)).all p = true) (hab : a ≤ b) (hbc : b ≤ c) :
    (List.range' a (c - a)).all p = true := by
  rw [range'_split a b c hab hbc, List.all_append, h1, h2]
  rfl

theorem rall_one {p : ℕ → Bool} {i : ℕ} (h : p i = true) : (List.range' i (i + 1 - i)).all p = true := by
  simp [h]

theorem rall_forall {p : ℕ → Bool} {n : ℕ} (h : (List.range' 0 (n - 0)).all p = true) :
    ∀ i, i < n → p i = true := by
  intro i hi
  exact List.all_eq_true.1 h i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

end BeatAvg.K8
