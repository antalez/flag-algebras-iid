import BeatAvg.Five.Gordan
import BeatAvg.Five.Cover
import Fast.Four.Checks.Cover

/-! Soundness of the sign-space cover, before interpreting its forms on samples. -/
namespace BeatAvg.Four
open Fast.Four Finset

def Feasible (p : Pattern) (x : Fin 4 → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i < 20,
    ∑ j : Fin 4, (((if p.testBit i then 1 else -1 : ℤ) * gapForm i j.val : ℤ) : ℝ) * x j < 0

theorem list_sum_get {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem exclusion_impossible {depth bits p : ℕ} {w : List (ℕ × ℕ)}
    (hd : depth ≤ 20) (h : exclusionOk depth bits w = true)
    (hprefix : ∀ j < depth, p.testBit j = bits.testBit j)
    {x : Fin 4 → ℝ} (hx : Feasible p x) : False := by
  cases w with
  | nil => simp [exclusionOk] at h
  | cons e ws =>
    simp only [exclusionOk, Bool.and_eq_true] at h
    have hw := h.1.2
    have hentry : ∀ i : Fin (e::ws).length,
        ((e::ws).get i).1 < depth ∧ 0 < ((e::ws).get i).2 := by
      intro i
      exact of_decide_eq_true ((List.all_eq_true.mp hw) _ ((e::ws).get_mem i))
    apply BeatAvg.Five.gordan_exclusion
      (fun (i : Fin (e::ws).length) (j : Fin 4) =>
        (((if bits.testBit ((e::ws).get i).1 then 1 else -1 : ℤ) *
          gapForm ((e::ws).get i).1 j.val : ℤ) : ℝ))
      (fun i => (((e::ws).get i).2 : ℝ)) x
    · intro i; positivity
    · refine ⟨⟨0, by simp⟩, ?_⟩
      exact_mod_cast (hentry ⟨0, by simp⟩).2
    · exact hx.1
    · intro i
      rw [← hprefix _ (hentry i).1]
      exact hx.2 _ (lt_of_lt_of_le (hentry i).1 hd)
    · intro j
      have hc := of_decide_eq_true ((List.all_eq_true.mp h.2) j.val (List.mem_range.mpr j.isLt))
      have hcr : (0 : ℝ) ≤ (((e::ws).map fun v =>
          (v.2 : ℤ) * (if bits.testBit v.1 then 1 else -1) * gapForm v.1 j.val).sum : ℤ) :=
        by exact_mod_cast hc
      simp only [Int.cast_list_sum, List.map_map, Function.comp_def] at hcr
      rw [list_sum_get] at hcr
      simpa only [Int.cast_mul, Int.cast_natCast, mul_assoc] using hcr

theorem cover_sound (tree : Cover) {patterns : Array Nat} {depth bits p : ℕ}
    (h : coverOk patterns tree depth bits = true)
    (hbits : bits < 2^depth) (hp : p < 2^20)
    (hprefix : ∀ j < depth, p.testBit j = bits.testBit j)
    {x : Fin 4 → ℝ} (hx : Feasible p x) : p ∈ patterns.toList := by
  induction tree generalizing depth bits with
  | excluded w =>
    simp only [coverOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact (exclusion_impossible h.1 h.2 hprefix hx).elim
  | retained i =>
    simp only [coverOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hd, hi⟩, he⟩ := h
    subst depth
    have hpb : p = bits := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < 20
      · exact hprefix j hj
      · have hpow : 2^20 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (hp.trans_le hpow),
          Nat.testBit_lt_two_pow (hbits.trans_le hpow)]
    have hm : patterns[i] ∈ patterns := Array.mem_of_getElem rfl
    have he' : patterns[i] = bits := by simpa [getElem!_pos patterns i hi] using he
    simpa [he', hpb] using hm
  | branch a b iha ihb =>
    simp only [coverOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpow : 2^(depth+1) = 2^depth*2 := by rw [pow_succ]
    cases hc : p.testBit depth with
    | false =>
      apply ihb h.2 (by rw [hpow]; omega)
      intro j hj
      by_cases hje : j = depth
      · subst j
        rw [hc, Nat.testBit_lt_two_pow hbits]
      · exact hprefix j (by omega)
    | true =>
      apply iha h.1.2 (by rw [hpow]; omega)
      intro j hj
      by_cases hje : j = depth
      · subst j
        rw [hc, Nat.add_comm bits, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow hbits]
        rfl
      · rw [Nat.add_comm bits, Nat.testBit_two_pow_add_gt (by omega)]
        exact hprefix j (by omega)

abbrev exists_bits := BeatAvg.Five.exists_bits

noncomputable def gapValue (i : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ j : Fin 4, (gapForm i j.val : ℝ)*x j

theorem signed_gapValue (p i : ℕ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 4, (((if p.testBit i then 1 else -1 : ℤ)*gapForm i j.val : ℤ) : ℝ)*x j) =
      (if p.testBit i then 1 else -1 : ℝ) * gapValue i x := by
  cases hh : p.testBit i <;> simp [hh, gapValue, Finset.mul_sum]

theorem exists_feasible (x : Fin 4 → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hne : ∀ i < 20, gapValue i x ≠ 0) :
    ∃ p < 2^20, Feasible p x ∧ ∀ i < 20, p.testBit i = decide (gapValue i x < 0) := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_bits (fun i => decide (gapValue i x < 0)) 20
  refine ⟨p, hp, ⟨hx, ?_⟩, hb⟩
  intro i hi
  rw [signed_gapValue, hb i hi]
  by_cases hn : gapValue i x < 0
  · simpa [hn]
  · have hh : 0 < gapValue i x := lt_of_le_of_ne (le_of_not_gt hn) (hne i hi).symm
    simp only [hn, decide_false, Bool.false_eq_true, ite_false, neg_mul, one_mul]
    linarith

/-- Every feasible twenty-bit sign pattern is one of the retained patterns. -/
theorem feasible_retained {p : Pattern} (hp : p < 2^20)
    {x : Fin 4 → ℝ} (hx : Feasible p x) : p ∈ Data.patterns.toList :=
  cover_sound Data.cover Checked.cover (by decide) hp (by omega) hx

end BeatAvg.Four
