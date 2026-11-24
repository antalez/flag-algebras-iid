import BeatAvg.Cert.Sorted
import BeatAvg.K8.SearchSound
import BeatAvg.K8.Hot

/-!
# Sum bits of a sorted sample as tests on the one-hot form of its packed pattern
-/

namespace BeatAvg.K8

open BeatAvg

theorem mem_triples {m : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ triples m ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < m := by
  obtain ⟨a, b, c⟩ := t
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', b', hb', c', hc', h⟩
    split_ifs at h with hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hlt.1, hlt.2, hc'⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨a, by omega, b, by omega, c, h3, ?_⟩
    simp [h1, h2]

theorem mem_ordQ : ∀ {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ},
    q ∈ ordQ n ↔ q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < n
  | 0, q => by simp [ordQ]
  | n + 1, q => by
    obtain ⟨a, b, c, d⟩ := q
    simp only [ordQ, List.mem_append, mem_ordQ (n := n), List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨t, ht, rfl, rfl, rfl, rfl⟩)
      · exact ⟨h1, h2, h3, by omega⟩
      · obtain ⟨h1, h2, h3⟩ := mem_triples.1 ht
        exact ⟨h1, h2, h3, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hd : d < n
      · exact Or.inl ⟨h1, h2, h3, hd⟩
      · have : d = n := by omega
        subst this
        exact Or.inr ⟨(a, b, c), mem_triples.2 ⟨h1, h2, h3⟩, rfl, rfl, rfl, rfl⟩

theorem ordQ8_length : (ordQ 8).length = 70 := by decide

theorem pat_length (w : ℕ → ℝ) : (pat 8 w).length = 70 := by
  rw [pat, List.length_map, ordQ8_length]

theorem pat_le_two (n : ℕ) (w : ℕ → ℝ) : ∀ t ∈ pat n w, t ≤ 2 := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  exact trit_le_two w q

theorem posQ8_lt {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ ordQ 8) : posQ8 q < 70 := by
  rw [← ordQ8_length]
  exact List.idxOf_lt_length_iff.2 hq

/-- The trit at the position of a quadruple. -/
theorem pat_pos (w : ℕ → ℝ) {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ ordQ 8) :
    (pat 8 w).getD (posQ8 q) 0 = trit w q := by
  have hi : (ordQ 8).idxOf q < (ordQ 8).length := List.idxOf_lt_length_iff.2 hq
  rw [pat, posQ8, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_idxOf hi]

theorem pat_getD_le (w : ℕ → ℝ) (p : ℕ) : (pat 8 w).getD p 0 ≤ 2 := by
  by_cases hp : p < (pat 8 w).length
  · rw [List.getD_eq_getElem _ _ hp]
    exact pat_le_two 8 w _ (List.getElem_mem hp)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

/-- The atom of a sum bit: a position below 70 and one of the sets `∅`, `{2}`, `{1, 2}`. -/
theorem sbAtom_spec (a b c d : ℕ) (hd : d < 8) (ha : a < 8) (hb : b < 8) (hc : c < 8) :
    (sbAtom a b c d).1 < 70 ∧
      ((sbAtom a b c d).2 = 0 ∨ (sbAtom a b c d).2 = 4 ∨ (sbAtom a b c d).2 = 6) := by
  have hz : max a (max b c) < 8 := by simp only [Nat.max_def]; split_ifs <;> omega
  simp only [sbAtom]
  split_ifs with h1 h2 h3
  · exact ⟨posQ8_lt (mem_ordQ.2 ⟨h1.1, h1.2, h2, hd⟩), Or.inr (Or.inr rfl)⟩
  · exact ⟨posQ8_lt (mem_ordQ.2 ⟨h1.1, h3.1, h3.2, hz⟩), Or.inr (Or.inl rfl)⟩
  · exact ⟨by norm_num, Or.inl rfl⟩
  · exact ⟨by norm_num, Or.inl rfl⟩

/-- A sum bit of a sorted sample is read off the trit of the atom. -/
theorem sb_atom {ω : Fin 8 → ℝ} (hω : SG8 ω) (a b c d : Fin 8) :
    (cfgOf ω).sb a b c d
      = (sbAtom a.val b.val c.val d.val).2.testBit
          ((pat 8 (extN ω)).getD (sbAtom a.val b.val c.val d.val).1 0) := by
  rw [cfgOf_eq_pat hω]
  have hz : max a.val (max b.val c.val) < 8 := by
    simp only [Nat.max_def]; split_ifs <;> omega
  show Fast.sbPat (patArr 8 (extN ω)) a.val b.val c.val d.val = _
  simp only [Fast.sbPat, sbAtom]
  split_ifs with h1 h2 h3
  · rw [patArr_idx8 (extN ω) h1.1 h1.2 h2 d.isLt, pat_pos _ (mem_ordQ.2 ⟨h1.1, h1.2, h2, d.isLt⟩)]
    have := trit_le_two (extN ω) (min a.val (min b.val c.val),
      a.val + b.val + c.val - min a.val (min b.val c.val) - max a.val (max b.val c.val),
      max a.val (max b.val c.val), d.val)
    generalize trit (extN ω) _ = t at this ⊢
    interval_cases t <;> simp <;> decide
  · rw [patArr_idx8 (extN ω) h1.1 h3.1 h3.2 hz, pat_pos _ (mem_ordQ.2 ⟨h1.1, h3.1, h3.2, hz⟩)]
    have := trit_le_two (extN ω) (min a.val (min b.val c.val),
      a.val + b.val + c.val - min a.val (min b.val c.val) - max a.val (max b.val c.val),
      d.val, max a.val (max b.val c.val))
    generalize trit (extN ω) _ = t at this ⊢
    interval_cases t <;> simp <;> decide
  · simp
  · simp

/-- The one-hot form of the packed pattern of a sample. -/
theorem hot_code (w : ℕ → ℝ) : hot (code 8 w) = hotL (pat 8 w) := by
  have := hotN_packL (pat 8 w) (pat_small 8 w)
  rwa [pat_length] at this

theorem sb_clearT {ω : Fin 8 → ℝ} (hω : SG8 ω) (a b c d : Fin 8) :
    (cfgOf ω).sb a b c d = true ↔
      Nat.land (hot (code 8 (extN ω))) (forbT (sbAtom a.val b.val c.val d.val)) = 0 := by
  obtain ⟨hp, hm⟩ := sbAtom_spec a.val b.val c.val d.val d.isLt a.isLt b.isLt c.isLt
  have ht := pat_getD_le (extN ω) (sbAtom a.val b.val c.val d.val).1
  rw [sb_atom hω, hot_code, nland, forbT, nshl,
    clear_atom (pat_le_two 8 _) (by rw [pat_length]; exact hp) (by omega)]
  generalize (pat 8 (extN ω)).getD _ 0 = t at ht ⊢
  rcases hm with h | h | h <;> rw [h] <;> interval_cases t <;> decide

theorem sb_clearF {ω : Fin 8 → ℝ} (hω : SG8 ω) (a b c d : Fin 8) :
    (cfgOf ω).sb a b c d = false ↔
      Nat.land (hot (code 8 (extN ω))) (forbF (sbAtom a.val b.val c.val d.val)) = 0 := by
  obtain ⟨hp, hm⟩ := sbAtom_spec a.val b.val c.val d.val d.isLt a.isLt b.isLt c.isLt
  rw [sb_atom hω, hot_code, nland, forbF, nshl,
    clear_atom (pat_le_two 8 _) (by rw [pat_length]; exact hp) (by omega)]

end BeatAvg.K8
