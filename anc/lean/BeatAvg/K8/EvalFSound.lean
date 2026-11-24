import BeatAvg.K8.EvalSound
import BeatAvg.K8.EvalF

/-!
# The evaluation specialised to a prefix agrees with the plain one

For the packed pattern `N = T + 4^35 · x` of a sample, `lamUVF t f T x = lamUV t N`, for grouped
tables `f` that satisfy their specification.
-/

open Function

namespace BeatAvg.K8

open BeatAvg
open Fast (Z4)

/-! ### Trits of the prefix and of the extension -/

theorem trS_even (M s : ℕ) (h : s % 2 = 0) : trS M s = tr M (s / 2) := by
  have : s = 2 * (s / 2) := by omega
  rw [this, trS_two]
  congr 1
  omega

theorem getD_le_two {L : List ℕ} (h : ∀ t ∈ L, t ≤ 2) (p : ℕ) : L.getD p 0 ≤ 2 := by
  by_cases hp : p < L.length
  · rw [List.getD_eq_getElem _ _ hp]; exact h _ (List.getElem_mem hp)
  · rw [List.getD_eq_default _ _ (by omega)]; omega

section Split

variable (w : ℕ → ℝ)

theorem pat7_length : (pat 7 w).length = 35 := by
  rw [pat, List.length_map]; decide

theorem extL7_length : (extL 7 w).length = 35 := by
  rw [extL, List.length_map]; decide

theorem extL_le_two (m : ℕ) : ∀ t ∈ extL m w, t ≤ 2 := by
  intro t ht
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
  exact trit_le_two w _

theorem code8_split : code 8 w = code 7 w + 4 ^ 35 * ext 7 w := by
  have := code_succ 7 w
  rwa [show (ordQ 7).length = 35 from by decide] at this

/-- A trit of the prefix. -/
theorem trS_old {s : ℕ} (h2 : s % 2 = 0) (h : s < 70) : trS (code 8 w) s = trS (code 7 w) s := by
  rw [trS_even _ _ h2, trS_even _ _ h2, code, code, tr_packL _ _ (pat_small 8 w),
    tr_packL _ _ (pat_small 7 w), pat_succ 7 w,
    List.getD_append _ _ _ _ (by rw [pat7_length]; omega)]

/-- A trit of the extension. -/
theorem trS_new {s : ℕ} (h2 : s % 2 = 0) (h : 70 ≤ s) :
    trS (code 8 w) s = trS (ext 7 w) (s - 70) := by
  rw [trS_even _ _ h2, trS_even _ _ (by omega), code, ext, tr_packL _ _ (pat_small 8 w),
    tr_packL _ _ (extL_small 7 w), pat_succ 7 w,
    List.getD_append_right _ _ _ _ (by rw [pat7_length]; omega), pat7_length]
  congr 1
  omega

/-- Beyond the prefix, its trits are zero. -/
theorem trS_T_zero {s : ℕ} (h2 : s % 2 = 0) (h : 70 ≤ s) : trS (code 7 w) s = 0 := by
  rw [trS_even _ _ h2, code, tr_packL _ _ (pat_small 7 w),
    List.getD_eq_default _ _ (by rw [pat7_length]; omega)]

theorem trS_le_two (n : ℕ) {s : ℕ} (h2 : s % 2 = 0) : trS (code n w) s ≤ 2 := by
  rw [trS_even _ _ h2, code, tr_packL _ _ (pat_small n w)]
  exact getD_le_two (pat_le_two n w) _

theorem trS_x_le_two {s : ℕ} (h2 : s % 2 = 0) : trS (ext 7 w) s ≤ 2 := by
  rw [trS_even _ _ h2, ext, tr_packL _ _ (extL_small 7 w)]
  exact getD_le_two (extL_le_two w 7) _

end Split

/-! ### The one-hot form splits -/

theorem hotL_append : ∀ (a b : List ℕ), hotL (a ++ b) = hotL a + 8 ^ a.length * hotL b
  | [], b => by simp [hotL]
  | t :: a, b => by
    rw [List.cons_append, hotL, hotL, hotL_append a b, List.length_cons, pow_succ]
    ring

theorem hotL_lt : ∀ {a : List ℕ}, (∀ t ∈ a, t ≤ 2) → hotL a < 8 ^ a.length
  | [], _ => by simp [hotL]
  | t :: a, h => by
    have ht : t ≤ 2 := h t List.mem_cons_self
    have ih := hotL_lt fun y hy => h y (List.mem_cons_of_mem _ hy)
    have : 2 ^ t ≤ 4 := by
      calc 2 ^ t ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) ht
        _ = 4 := by norm_num
    rw [hotL, List.length_cons, pow_succ]
    omega

theorem land_split {a k : ℕ} (ha : a < 2 ^ k) (b F : ℕ) :
    (a + 2 ^ k * b) &&& F = (a &&& (F % 2 ^ k)) + 2 ^ k * (b &&& (F >>> k)) := by
  have hlt : a &&& (F % 2 ^ k) < 2 ^ k := lt_of_le_of_lt Nat.and_le_left ha
  apply Nat.eq_of_testBit_eq
  intro j
  have e1 : a + 2 ^ k * b = 2 ^ k * b + a := by ring
  have e2 : (a &&& (F % 2 ^ k)) + 2 ^ k * (b &&& (F >>> k))
      = 2 ^ k * (b &&& (F >>> k)) + (a &&& (F % 2 ^ k)) := by ring
  rw [e1, e2, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha,
    Nat.testBit_two_pow_mul_add _ hlt]
  by_cases hj : j < k
  · simp [hj]
  · simp only [hj, ite_false, Nat.testBit_and, Nat.testBit_shiftRight]
    congr 2
    omega

/-- A condition on the whole pattern is a condition on the prefix and one on the extension. -/
theorem clr_split {a k : ℕ} (ha : a < 2 ^ k) (b F : ℕ) :
    clr (a + 2 ^ k * b) F = (clr a (Nat.land F (2 ^ k - 1)) && clr b (Nat.shiftRight F k)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, clr_iff, clr_iff, clr_iff, nland, nland, nland, nshr,
    land_split ha, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : a &&& (F % 2 ^ k) < 2 ^ k := lt_of_le_of_lt Nat.and_le_left ha
  constructor
  · intro h
    have h1 : a &&& (F % 2 ^ k) = 0 := by
      have := congrArg (· % 2 ^ k) h
      simp only [Nat.add_mul_mod_self_left, Nat.zero_mod] at this
      rwa [Nat.mod_eq_of_lt hlt] at this
    rw [h1, zero_add] at h
    exact ⟨h1, by
      rcases Nat.mul_eq_zero.1 h with h2 | h2
      · exact absurd h2 (by positivity)
      · exact h2⟩
  · rintro ⟨h1, h2⟩
    have h2' : b &&& (F >>> k) = 0 := h2
    rw [h1, h2']; simp

theorem hot_split (w : ℕ → ℝ) :
    hot (code 8 w) = hotN 35 (code 7 w) + 2 ^ 105 * hotN 35 (ext 7 w) := by
  have h7 := hotN_packL (pat 7 w) (pat_small 7 w)
  have hx := hotN_packL (extL 7 w) (extL_small 7 w)
  rw [pat7_length] at h7
  rw [extL7_length] at hx
  rw [hot_code, pat_succ, hotL_append, pat7_length, code, ext, h7, hx]
  norm_num

theorem hotT_lt (w : ℕ → ℝ) : hotN 35 (code 7 w) < 2 ^ 105 := by
  have h7 := hotN_packL (pat 7 w) (pat_small 7 w)
  rw [pat7_length] at h7
  rw [code, h7]
  have := hotL_lt (pat_le_two 7 w)
  rw [pat7_length] at this
  calc hotL (pat 7 w) < 8 ^ 35 := this
    _ = 2 ^ 105 := by norm_num

/-- The condition `F` on the pattern, from its parts on the prefix and on the extension. -/
theorem clr_hot (w : ℕ → ℝ) (F : ℕ) :
    clr (hot (code 8 w)) F
      = (clr (hotN 35 (code 7 w)) (Nat.land F lowM) && clr (hotN 35 (ext 7 w)) (Nat.shiftRight F 105)) := by
  rw [hot_split, clr_split (hotT_lt w)]
  rfl

theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

theorem ble_false {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff]
  intro hc
  exact absurd (Nat.le_of_ble_eq_true hc) (by omega)

/-! ### Codes of the five-point subsets -/

/-- Shape of an entry of the table of positions: even offsets; the first in the prefix; the four
others all in the prefix or all beyond. -/
def psOk (ps : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (ps.1 % 2 = 0) && decide (ps.2.1 % 2 = 0) && decide (ps.2.2.1 % 2 = 0) &&
    decide (ps.2.2.2.1 % 2 = 0) && decide (ps.2.2.2.2 % 2 = 0) && decide (ps.1 < 70) &&
    ((decide (ps.2.1 < 70) && decide (ps.2.2.1 < 70) && decide (ps.2.2.2.1 < 70) &&
        decide (ps.2.2.2.2 < 70)) ||
      (decide (70 ≤ ps.2.1) && decide (70 ≤ ps.2.2.1) && decide (70 ≤ ps.2.2.2.1) &&
        decide (70 ≤ ps.2.2.2.2)))

/-- The part of a code that comes from the extension. -/
def xd (x : ℕ) (ps : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  bif Nat.ble 70 ps.2.1 then
    3 * (trS x (ps.2.1 - 70) + 3 * (trS x (ps.2.2.1 - 70) + 3 * (trS x (ps.2.2.2.1 - 70)
      + 3 * trS x (ps.2.2.2.2 - 70))))
  else 0

def packH (x : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | ps :: l => xd x ps + 256 * packH x l

theorem code5_def (M : ℕ) (ps : ℕ × ℕ × ℕ × ℕ × ℕ) :
    code5 M ps = trS M ps.1 + 3 * (trS M ps.2.1 + 3 * (trS M ps.2.2.1 + 3 * (trS M ps.2.2.2.1
      + 3 * trS M ps.2.2.2.2))) := rfl

section Codes

variable (w : ℕ → ℝ)

theorem code5_split {ps : ℕ × ℕ × ℕ × ℕ × ℕ} (h : psOk ps = true) :
    code5 (code 8 w) ps = code5 (code 7 w) ps + xd (ext 7 w) ps := by
  simp only [psOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, h0⟩, hc⟩ := h
  rw [code5_def, code5_def, xd, trS_old w e0 h0]
  rcases hc with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · rw [trS_old w e1 h1, trS_old w e2 h2, trS_old w e3 h3, trS_old w e4 h4]
    have : Nat.ble 70 ps.2.1 = false := ble_false h1
    simp [this]
  · rw [trS_new w e1 h1, trS_new w e2 h2, trS_new w e3 h3, trS_new w e4 h4,
      trS_T_zero w e1 h1, trS_T_zero w e2 h2, trS_T_zero w e3 h3, trS_T_zero w e4 h4]
    have : Nat.ble 70 ps.2.1 = true := ble_true h1
    simp only [this, Bool.cond_true]
    ring

theorem codes_split : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)), l.all psOk = true →
    codes (code 8 w) l = codes (code 7 w) l + packH (ext 7 w) l
  | [], _ => rfl
  | ps :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [codes_cons, codes_cons, packH, code5_split w h.1, codes_split l h.2]
    ring

theorem codesX_spec (x : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (o : ℕ),
    codesX x (sNewSpec l o) = 2 ^ o * packH x l
  | [], o => by simp [sNewSpec, codesX, packH]
  | ps :: l, o => by
    rw [sNewSpec, packH, xd]
    cases h : Nat.ble 70 ps.2.1
    · simp only [Bool.cond_false, codesX_spec x l (o + 8), pow_add]
      ring
    · simp only [Bool.cond_true, codesX, codesX_spec x l (o + 8), nadd, nmul, nshl,
        Nat.shiftLeft_eq, pow_add]
      ring

/-- The codes of the sample are those of the prefix plus the part from the extension. -/
theorem codes_fast (h : sub5Spec.all psOk = true) :
    Nat.add (codes (code 7 w) sub5Spec) (codesX (ext 7 w) (sNewSpec sub5Spec 0))
      = codes (code 8 w) sub5Spec := by
  rw [codesX_spec, codes_split w _ h, nadd]
  simp

theorem code5_lt {M : ℕ} (hM : ∀ s, s % 2 = 0 → trS M s ≤ 2) {ps : ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : psOk ps = true) : code5 M ps < 256 := by
  simp only [psOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, -⟩, -⟩ := h
  rw [code5_def]
  have := hM _ e0
  have := hM _ e1
  have := hM _ e2
  have := hM _ e3
  have := hM _ e4
  omega

/-- Digit `S` of the packed codes, for the sample (`n = 8`) or its prefix (`n = 7`). -/
theorem digit_codes (n : ℕ) (h : sub5Spec.all psOk = true) {S : ℕ} (hS : S < 56) :
    digit (codes (code n w) sub5Spec) (8 * S) = code5 (code n w) (sub5Spec.getD S (0, 0, 0, 0, 0)) := by
  rw [digit, codes_digit _ _ S ?_ (by rw [sub5Spec, List.length_map, subs5_length]; exact hS)]
  intro ps hps
  exact code5_lt (fun s hs => trS_le_two w n hs) (List.all_eq_true.1 h ps hps)

end Codes

/-! ### Regrouping a sum by a key -/

theorem sum_ite_mem (c k0 : ℕ) : ∀ (ks : List ℕ), ks.Nodup → k0 ∈ ks →
    (ks.map fun k => if Nat.beq k0 k = true then c else 0).sum = c
  | [], _, h => by simp at h
  | k :: ks, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases hk : k0 = k
    · subst hk
      have hz : (ks.map fun k => if Nat.beq k0 k = true then c else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
        have : k0 ≠ k := fun e => hnd.1 (e ▸ hk)
        simp [this]
      rw [hz, Nat.beq_refl]
      simp
    · have hmem : k0 ∈ ks := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h hk
        · exact h
      rw [sum_ite_mem c k0 ks hnd.2 hmem]
      simp [hk]

theorem regroup {α : Type} (κ : α → ℕ) (f : α → ℕ) (ks : List ℕ) (hnd : ks.Nodup) :
    ∀ (L : List α), (∀ a ∈ L, κ a ∈ ks) →
    (L.map f).sum = (ks.map fun k => ((L.filter fun a => Nat.beq (κ a) k).map f).sum).sum
  | [], _ => by simp
  | a :: L, h => by
    have ih := regroup κ f ks hnd L fun b hb => h b (List.mem_cons_of_mem _ hb)
    have hstep : ∀ k, (((a :: L).filter fun a => Nat.beq (κ a) k).map f).sum
        = (if Nat.beq (κ a) k = true then f a else 0)
          + ((L.filter fun a => Nat.beq (κ a) k).map f).sum := by
      intro k
      rw [List.filter_cons]
      split_ifs <;> simp
    simp only [hstep]
    rw [List.sum_map_add, sum_ite_mem (f a) (κ a) ks hnd (h a List.mem_cons_self), ← ih,
      List.map_cons, List.sum_cons]

theorem sumL_eq {α : Type} (f : α → ℕ) : ∀ l : List α, sumL f l = (l.map f).sum
  | [] => rfl
  | a :: l => by rw [sumL, sumL_eq f l, List.map_cons, List.sum_cons, nadd]

theorem pick3_eq {α : Type} {τ : ℕ} (h : τ ≤ 2) (f : ℕ → α) : pick3 τ f = f τ := by
  interval_cases τ <;> rfl

/-! ### The new subsets -/

theorem mem_sNewSpec : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (o : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ),
    s ∈ sNewSpec l o → ∃ i, i < l.length ∧ 70 ≤ (l.getD i (0, 0, 0, 0, 0)).2.1 ∧
      s = (o + 8 * i, (l.getD i (0, 0, 0, 0, 0)).2.1 - 70, (l.getD i (0, 0, 0, 0, 0)).2.2.1 - 70,
        (l.getD i (0, 0, 0, 0, 0)).2.2.2.1 - 70, (l.getD i (0, 0, 0, 0, 0)).2.2.2.2 - 70)
  | [], _, _, h => by simp [sNewSpec] at h
  | ps :: l, o, s, h => by
    rw [sNewSpec] at h
    cases hb : Nat.ble 70 ps.2.1
    · rw [hb, Bool.cond_false] at h
      obtain ⟨i, hi, h1, h2⟩ := mem_sNewSpec l (o + 8) s h
      refine ⟨i + 1, by simpa using hi, by simpa using h1, ?_⟩
      rw [h2]
      simp only [List.getD_cons_succ]
      congr 1
      ring
    · rw [hb, Bool.cond_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp, by simpa using Nat.le_of_ble_eq_true hb, by simp⟩
      · obtain ⟨i, hi, h1, h2⟩ := mem_sNewSpec l (o + 8) s h
        refine ⟨i + 1, by simpa using hi, by simpa using h1, ?_⟩
        rw [h2]
        simp only [List.getD_cons_succ]
        congr 1
        ring

section Digits

variable (w : ℕ → ℝ) (hsub : sub5Spec.all psOk = true)

include hsub in
theorem psOk_getD {S : ℕ} (hS : S < 56) : psOk (sub5Spec.getD S (0, 0, 0, 0, 0)) = true := by
  have hl : S < sub5Spec.length := by rw [sub5Spec, List.length_map, subs5_length]; exact hS
  rw [List.getD_eq_getElem _ _ hl]
  exact List.all_eq_true.1 hsub _ (List.getElem_mem hl)

include hsub in
/-- The code of an old subset is the same for the sample and its prefix. -/
theorem digit_old {S : ℕ} (hS : S < 56) (h : (sub5Spec.getD S (0, 0, 0, 0, 0)).2.1 < 70) :
    digit (codes (code 8 w) sub5Spec) (8 * S) = digit (codes (code 7 w) sub5Spec) (8 * S) := by
  rw [digit_codes w 8 hsub hS, digit_codes w 7 hsub hS, code5_split w (psOk_getD hsub hS), xd,
    ble_false h]
  simp

include hsub in
/-- The code of a new subset, from the code of its old quadruple and its four new trits. -/
theorem digit_new {S : ℕ} (hS : S < 56) (h : 70 ≤ (sub5Spec.getD S (0, 0, 0, 0, 0)).2.1) :
    digit (codes (code 8 w) sub5Spec) (8 * S)
      = codeOf (codes (code 7 w) sub5Spec) (8 * S)
          (trS (ext 7 w) ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.1 - 70))
          (trS (ext 7 w) ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.1 - 70))
          (trS (ext 7 w) ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.1 - 70))
          (trS (ext 7 w) ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.2 - 70)) := by
  have hok := psOk_getD hsub hS
  rw [digit_codes w 8 hsub hS, codeOf, digit_codes w 7 hsub hS, code5_split w hok, xd, ble_true h]
  simp only [Bool.cond_true, nadd, nmul]

end Digits

/-! ### The grouped tables satisfy their specification -/

/-- Facts about the grouped tables `f` and the tables `t`; each is checked by evaluation. -/
structure TfOk (t : Tb) (f : Tf) (quads masks : List ℕ) : Prop where
  sNew : f.sNew = sNewSpec t.sub5 0
  psok : t.sub5.all psOk = true
  newOK : ∀ S, S < 56 → isNewS (8 * S) = Nat.ble 70 (t.sub5.getD S (0, 0, 0, 0, 0)).2.1
  sqG : f.sqG = f.sNew.map fun s => t.sq.filter fun e => Nat.beq (sqKey e) s.1
  sqR : f.sqR = t.sq.filter fun e => Nat.beq (sqKey e) 1000
  sqK : ∀ e ∈ t.sq, sqKey e ∈ f.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ [1000]
  sqSh : ∀ e ∈ t.sq, e.1 % 8 = 0 ∧ e.1 / 8 < 56 ∧ e.2.2.1 % 8 = 0 ∧ e.2.2.1 / 8 < 56
  sqNd : (f.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ [1000]).Nodup
  degG : f.degG = f.sNew.map fun s => t.deg.filter fun e => Nat.beq (degKey e) s.1
  degQ : f.degQ = quads.map fun k =>
    (k - 70, t.deg.filter fun e => Nat.beq (degKey e) (Nat.add 2000 k))
  degK : ∀ e ∈ t.deg, degKey e ∈ f.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1)
    ++ quads.map (Nat.add 2000)
  degNd : (f.sNew.map (fun s : ℕ × ℕ × ℕ × ℕ × ℕ => s.1) ++ quads.map (Nat.add 2000)).Nodup
  degSh : ∀ e ∈ t.deg, e.1 % 8 = 0 ∧ e.1 / 8 < 56 ∧ e.2.2.1 % 2 = 0
  quadsOk : ∀ k ∈ quads, 70 ≤ k ∧ k % 2 = 0
  kqLen : f.kq.length = f.sNew.length
  kqOk : ∀ p ∈ f.sNew.zip f.kq, p.2 % 2 = 0 ∧
    ∀ e ∈ t.deg, degKey e = p.1.1 → e.2.2.1 < 70 ∨ e.2.2.1 = 70 + p.2
  thrLen : ∀ e ∈ t.thr, e.2.length = 8
  thrIncl : ∀ e ∈ t.thr, ∀ fq ∈ e.2, Nat.land fq.1 e.1 = e.1 ∧ Nat.land fq.2.1 e.1 = e.1 ∧
    Nat.land fq.2.2 e.1 = e.1
  thrG : f.thrG = masks.map fun m =>
    (m, ((thrFlat t).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).length,
      ((thrFlat t).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).map fun it =>
        (Nat.land it.1 lowM, it.2))
  thrK : ∀ it ∈ thrFlat t, Nat.shiftRight it.1 105 ∈ masks
  thrNd : masks.Nodup
  objO : f.objO = t.obj.filter fun m => Nat.beq (Nat.shiftRight m 105) 0
  objN : f.objN = (t.obj.filter fun m => !(Nat.beq (Nat.shiftRight m 105) 0)).map fun m =>
    Nat.shiftRight m 105
  objSh : ∀ m ∈ t.obj, Nat.shiftRight m 105 = 0 ∨ Nat.land m lowM = 0

theorem sqNew_map (t : Tb) (CT x : ℕ) (G : ℕ × ℕ × ℕ × ℕ × ℕ → List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ ss : List (ℕ × ℕ × ℕ × ℕ × ℕ),
    sqNew t CT x ss (ss.map G) = (ss.map fun s => pick4 x s (sqLeaf t CT s.1 (G s))).sum
  | [] => rfl
  | s :: ss => by
    rw [List.map_cons, sqNew, sqNew_map t CT x G ss, List.map_cons, List.sum_cons, nadd]

section Fast

variable {t : Tb} {f : Tf} {quads masks : List ℕ} (ht : TbOk t) (hf : TfOk t f quads masks)
  (w : ℕ → ℝ)

include ht hf in
/-- Facts about a new subset `s` of the list. -/
theorem sNew_facts {s : ℕ × ℕ × ℕ × ℕ × ℕ} (hs : s ∈ f.sNew) :
    ∃ S, S < 56 ∧ s.1 = 8 * S ∧ isNewS s.1 = true ∧
      s.2.1 % 2 = 0 ∧ s.2.2.1 % 2 = 0 ∧ s.2.2.2.1 % 2 = 0 ∧ s.2.2.2.2 % 2 = 0 ∧
      digit (codes (code 8 w) t.sub5) s.1
        = codeOf (codes (code 7 w) t.sub5) s.1 (trS (ext 7 w) s.2.1) (trS (ext 7 w) s.2.2.1)
            (trS (ext 7 w) s.2.2.2.1) (trS (ext 7 w) s.2.2.2.2) := by
  have hsub := hf.psok
  rw [ht.sub5] at hsub
  rw [hf.sNew, ht.sub5] at hs
  obtain ⟨S, hS, hnew, rfl⟩ := mem_sNewSpec _ _ _ hs
  have hS' : S < 56 := by rwa [sub5Spec, List.length_map, subs5_length] at hS
  have hok := psOk_getD hsub hS'
  simp only [psOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, h0⟩, hc⟩ := hok
  have hc' : 70 ≤ (sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.1
      ∧ 70 ≤ (sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.1
      ∧ 70 ≤ (sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.2 := by
    rcases hc with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · omega
    · exact ⟨h2, h3, h4⟩
  have hnew' := hf.newOK S hS'
  rw [ht.sub5, ble_true hnew] at hnew'
  have hc1 := hc'.1
  have hc2 := hc'.2.1
  have hc3 := hc'.2.2
  refine ⟨S, hS', by simp, by simpa using hnew', ?_, ?_, ?_, ?_, ?_⟩
  · show ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.1 - 70) % 2 = 0
    omega
  · show ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.1 - 70) % 2 = 0
    omega
  · show ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.1 - 70) % 2 = 0
    omega
  · show ((sub5Spec.getD S (0, 0, 0, 0, 0)).2.2.2.2 - 70) % 2 = 0
    omega
  · simp only [zero_add, ht.sub5]
    exact digit_new w hsub hS' hnew

include ht hf in
/-- The code of an old subset is read in the codes of the prefix. -/
theorem old_digit {o : ℕ} (h8 : o % 8 = 0) (h56 : o / 8 < 56) (hold : isNewS o = false) :
    digit (codes (code 8 w) t.sub5) o = digit (codes (code 7 w) t.sub5) o := by
  have hsub := hf.psok
  rw [ht.sub5] at hsub
  have ho : o = 8 * (o / 8) := by omega
  have hnew := hf.newOK (o / 8) h56
  rw [← ho, hold, ht.sub5] at hnew
  rw [ht.sub5, ho]
  apply digit_old w hsub h56
  by_contra hc
  rw [ble_true (by omega)] at hnew
  exact absurd hnew (by simp)

include ht hf in
/-- One group of square terms: the terms whose only new subset is `s`. -/
theorem sq_group {s : ℕ × ℕ × ℕ × ℕ × ℕ} (hs : s ∈ f.sNew) :
    pick4 (ext 7 w) s (sqLeaf t (codes (code 7 w) t.sub5) s.1
        (t.sq.filter fun e => Nat.beq (sqKey e) s.1))
      = ((t.sq.filter fun e => Nat.beq (sqKey e) s.1).map
          (sqEnt t (codes (code 8 w) t.sub5))).sum := by
  obtain ⟨S, hS, hs1, hnew, e1, e2, e3, e4, hdig⟩ := sNew_facts ht hf w hs
  rw [pick4, pick3_eq (trS_x_le_two w e1), pick3_eq (trS_x_le_two w e2),
    pick3_eq (trS_x_le_two w e3), pick3_eq (trS_x_le_two w e4), sqLeaf, sumL_eq]
  congr 1
  refine List.map_congr_left fun e he => ?_
  obtain ⟨hmem, hkey⟩ := List.mem_filter.1 he
  have hkey' : sqKey e = s.1 := Nat.eq_of_beq_eq_true hkey
  obtain ⟨a8, a56, b8, b56⟩ := hf.sqSh e hmem
  have hlt : s.1 < 1000 := by omega
  -- the two sides: the new one has the code of `s`, the other is old
  have side : ∀ o, o % 8 = 0 → o / 8 < 56 → (o = s.1 ∨ isNewS o = false) →
      (bif Nat.beq o s.1 then codeOf (codes (code 7 w) t.sub5) s.1 (trS (ext 7 w) s.2.1)
          (trS (ext 7 w) s.2.2.1) (trS (ext 7 w) s.2.2.2.1) (trS (ext 7 w) s.2.2.2.2)
        else digit (codes (code 7 w) t.sub5) o) = digit (codes (code 8 w) t.sub5) o := by
    intro o h8 h56 h
    rcases h with rfl | h
    · rw [Nat.beq_refl, Bool.cond_true, hdig]
    · have hne : Nat.beq o s.1 = false := by
        rw [Bool.eq_false_iff]
        intro hc
        rw [Nat.eq_of_beq_eq_true hc, hnew] at h
        exact absurd h (by simp)
      rw [hne, Bool.cond_false, old_digit ht hf w h8 h56 h]
  have hA : e.1 = s.1 ∨ isNewS e.1 = false := by
    unfold sqKey at hkey'
    cases hx : isNewS e.1
    · exact Or.inr rfl
    · rw [hx, Bool.cond_true] at hkey'
      cases hy : isNewS e.2.2.1
      · rw [hy, Bool.cond_false] at hkey'; exact Or.inl hkey'
      · rw [hy, Bool.cond_true] at hkey'; omega
  have hB : e.2.2.1 = s.1 ∨ isNewS e.2.2.1 = false := by
    unfold sqKey at hkey'
    cases hx : isNewS e.1
    · rw [hx, Bool.cond_false] at hkey'; exact Or.inl hkey'
    · rw [hx, Bool.cond_true] at hkey'
      cases hy : isNewS e.2.2.1
      · exact Or.inr rfl
      · rw [hy, Bool.cond_true] at hkey'; omega
  simp only [sqEntO, sqEnt, side e.1 a8 a56 hA, side e.2.2.1 b8 b56 hB]
  rfl

include ht hf in
/-- **The square sum.** -/
theorem sq_fast :
    Nat.add (sqNew t (codes (code 7 w) t.sub5) (ext 7 w) f.sNew f.sqG)
        (sumL (sqEnt t (codes (code 8 w) t.sub5)) f.sqR)
      = sqAcc t (codes (code 8 w) t.sub5) t.sq 0 := by
  rw [sqAcc_eq, zero_add, regroup sqKey _ _ hf.sqNd t.sq hf.sqK, List.map_append,
    List.sum_append, hf.sqG, sqNew_map, sumL_eq, hf.sqR, nadd, List.map_map]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  congr 1
  refine List.map_congr_left fun s hs => ?_
  exact sq_group ht hf w hs

theorem degNew_map (t : Tb) (T CT x : ℕ) (G : ℕ × ℕ × ℕ × ℕ × ℕ → List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ (ss : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (ks : List ℕ), ks.length = ss.length →
    degNew t T CT x ss ks (ss.map G) = ((ss.zip ks).map fun p =>
      pick4 x p.1 fun a b c d => pick3 (trS x p.2) (degLeaf t T CT p.1.1 (G p.1) a b c d)).sum
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | s :: ss, k :: ks, h => by
    rw [List.map_cons, degNew, degNew_map t T CT x G ss ks (by simpa using h), List.zip_cons_cons,
      List.map_cons, List.sum_cons, nadd]

theorem degOld_map (t : Tb) (T CT x : ℕ) (G : ℕ → List (ℕ × ℕ × ℕ × ℕ)) : ∀ (qs : List ℕ),
    degOld t T CT x (qs.map fun k => (k - 70, G k)) = (qs.map fun k =>
      pick3 (trS x (k - 70)) fun τ => sumL (degEntO t T CT 1000 0 τ) (G k)).sum
  | [] => rfl
  | k :: qs => by
    rw [List.map_cons, degOld, degOld_map t T CT x G qs, List.map_cons, List.sum_cons, nadd]

include ht hf in
/-- One group of degree terms with a new subset. -/
theorem deg_group_new {p : (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ} (hp : p ∈ f.sNew.zip f.kq) :
    (pick4 (ext 7 w) p.1 fun a b c d => pick3 (trS (ext 7 w) p.2)
        (degLeaf t (code 7 w) (codes (code 7 w) t.sub5) p.1.1
          (t.deg.filter fun e => Nat.beq (degKey e) p.1.1) a b c d))
      = ((t.deg.filter fun e => Nat.beq (degKey e) p.1.1).map
          (degEnt t (code 8 w) (codes (code 8 w) t.sub5))).sum := by
  have hs : p.1 ∈ f.sNew := (List.of_mem_zip hp).1
  obtain ⟨S, hS, hs1, hnew, e1, e2, e3, e4, hdig⟩ := sNew_facts ht hf w hs
  obtain ⟨hk2, hkq⟩ := hf.kqOk p hp
  rw [pick4, pick3_eq (trS_x_le_two w e1), pick3_eq (trS_x_le_two w e2),
    pick3_eq (trS_x_le_two w e3), pick3_eq (trS_x_le_two w e4), pick3_eq (trS_x_le_two w hk2),
    degLeaf, sumL_eq]
  congr 1
  refine List.map_congr_left fun e he => ?_
  obtain ⟨hmem, hkey⟩ := List.mem_filter.1 he
  have hkey' : degKey e = p.1.1 := Nat.eq_of_beq_eq_true hkey
  obtain ⟨a8, a56, q2⟩ := hf.degSh e hmem
  have he1 : e.1 = p.1.1 := by
    unfold degKey at hkey'
    cases hx : isNewS e.1
    · rw [hx, Bool.cond_false, nadd] at hkey'; omega
    · rw [hx, Bool.cond_true] at hkey'; exact hkey'
  have hcls : (bif Nat.beq e.1 p.1.1 then codeOf (codes (code 7 w) t.sub5) p.1.1
        (trS (ext 7 w) p.1.2.1) (trS (ext 7 w) p.1.2.2.1) (trS (ext 7 w) p.1.2.2.2.1)
        (trS (ext 7 w) p.1.2.2.2.2)
      else digit (codes (code 7 w) t.sub5) e.1) = digit (codes (code 8 w) t.sub5) e.1 := by
    rw [he1, Nat.beq_refl, Bool.cond_true, hdig]
  have htr : (bif Nat.ble 70 e.2.2.1 then trS (ext 7 w) p.2 else trS (code 7 w) e.2.2.1)
      = trS (code 8 w) e.2.2.1 := by
    rcases hkq e hmem hkey' with h | h
    · rw [ble_false h, Bool.cond_false, trS_old w q2 h]
    · rw [ble_true (by omega), Bool.cond_true, trS_new w q2 (by omega), h]
      congr 1
      omega
  simp only [degEntO, degEnt, hcls, htr]
  rfl

include ht hf in
/-- One group of degree terms with an old subset: those of a new quadruple. -/
theorem deg_group_old {k : ℕ} (hk : k ∈ quads) :
    (pick3 (trS (ext 7 w) (k - 70)) fun τ => sumL (degEntO t (code 7 w)
        (codes (code 7 w) t.sub5) 1000 0 τ)
          (t.deg.filter fun e => Nat.beq (degKey e) (Nat.add 2000 k)))
      = ((t.deg.filter fun e => Nat.beq (degKey e) (Nat.add 2000 k)).map
          (degEnt t (code 8 w) (codes (code 8 w) t.sub5))).sum := by
  obtain ⟨hk70, hk2⟩ := hf.quadsOk k hk
  rw [pick3_eq (trS_x_le_two w (by omega)), sumL_eq]
  congr 1
  refine List.map_congr_left fun e he => ?_
  obtain ⟨hmem, hkey⟩ := List.mem_filter.1 he
  have hkey' : degKey e = 2000 + k := Nat.eq_of_beq_eq_true hkey
  obtain ⟨a8, a56, q2⟩ := hf.degSh e hmem
  have hold : isNewS e.1 = false ∧ e.2.2.1 = k := by
    unfold degKey at hkey'
    cases hx : isNewS e.1
    · rw [hx, Bool.cond_false, nadd] at hkey'; exact ⟨rfl, by omega⟩
    · rw [hx, Bool.cond_true] at hkey'; omega
  have hne : Nat.beq e.1 1000 = false := by
    rw [Bool.eq_false_iff]
    intro hc
    have := Nat.eq_of_beq_eq_true hc
    omega
  have htr : (bif Nat.ble 70 e.2.2.1 then trS (ext 7 w) (k - 70) else trS (code 7 w) e.2.2.1)
      = trS (code 8 w) e.2.2.1 := by
    rw [hold.2, ble_true hk70, Bool.cond_true, trS_new w hk2 hk70]
  simp only [degEntO, degEnt, hne, Bool.cond_false, htr, ← old_digit ht hf w a8 a56 hold.1]
  rfl

include ht hf in
/-- **The degree sum.** -/
theorem deg_fast :
    Nat.add (degNew t (code 7 w) (codes (code 7 w) t.sub5) (ext 7 w) f.sNew f.kq f.degG)
        (degOld t (code 7 w) (codes (code 7 w) t.sub5) (ext 7 w) f.degQ)
      = degAcc t (code 8 w) (codes (code 8 w) t.sub5) t.deg 0 := by
  rw [degAcc_eq, zero_add, regroup degKey _ _ hf.degNd t.deg hf.degK, List.map_append,
    List.sum_append, hf.degG, degNew_map _ _ _ _ _ _ _ hf.kqLen, hf.degQ, degOld_map, nadd,
    List.map_map, List.map_map]
  congr 1
  · have hz : f.sNew.map (fun s => ((t.deg.filter fun e => Nat.beq (degKey e) s.1).map
          (degEnt t (code 8 w) (codes (code 8 w) t.sub5))).sum)
        = (f.sNew.zip f.kq).map fun p => ((t.deg.filter fun e => Nat.beq (degKey e) p.1.1).map
          (degEnt t (code 8 w) (codes (code 8 w) t.sub5))).sum := by
      have h1 := List.map_fst_zip (l₁ := f.sNew) (l₂ := f.kq) (by rw [hf.kqLen])
      conv_lhs => rw [← h1]
      rw [List.map_map]
      rfl
    simp only [Function.comp_def]
    rw [hz]
    congr 1
    exact List.map_congr_left fun p hp => deg_group_new ht hf w hp
  · simp only [Function.comp_def]
    congr 1
    exact List.map_congr_left fun k hk => deg_group_old ht hf w hk

/-! ### Threshold sums -/

/-- The items of one arrangement: forbidden bits and entry. -/
def thrItems (TT : List (ℕ × ℕ × ℕ)) (e : ℕ × List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  (e.2.zip TT).flatMap fun p => [(p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)]

theorem thrFlat_eq (t : Tb) : thrFlat t = t.thr.flatMap (thrItems t.TT) := rfl

theorem thrL_map (H z : ℕ) : ∀ (fs es : List (ℕ × ℕ × ℕ)),
    thrL H z fs es = ((fs.zip es).flatMap fun p =>
      [(p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)]).map fun it => sel H it.1 it.2 z
  | [], _ => by simp [thrL]
  | _ :: _, [] => by simp [thrL]
  | f :: fs, e :: es => by
    simp only [thrL, List.zip_cons_cons, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil, thrL_map H z fs es, List.cons_append, List.nil_append]

theorem sum_flatMap_nat {α β : Type} (g : β → ℕ) (f : α → List β) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap_nat g f l]

theorem sum_flatMap' {α : Type} (f : α → List ℕ) : ∀ l : List α,
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, sum_flatMap' f l]

theorem sum_const {α : Type} (g : α → ℕ) (c : ℕ) : ∀ l : List α, (∀ a ∈ l, g a = c) →
    (l.map g).sum = l.length * c
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_const g c l fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

theorem clr_incl {H F R : ℕ} (h : Nat.land F R = R) (hR : clr H R = false) : clr H F = false := by
  rw [Bool.eq_false_iff] at hR ⊢
  intro hF
  apply hR
  rw [clr_iff, nland] at hF ⊢
  have h' : F &&& R = R := h
  rw [← h', ← Nat.and_assoc, hF, Nat.zero_and]

include ht hf in
/-- The threshold sum as a sum over all items. -/
theorem thr_flat (H : ℕ) :
    thrAcc t H (zero8 t.wT t.offT) (Nat.mul 24 (zero8 t.wT t.offT)) t.thr 0
      = ((thrFlat t).map fun it => sel H it.1 it.2 (zero8 t.wT t.offT)).sum := by
  rw [thrAcc_eq, zero_add, thrFlat_eq, sum_flatMap_nat, sum_flatMap']
  congr 1
  refine List.map_congr_left fun e he => ?_
  have hlen := hf.thrLen e he
  have hTT := ht.tt.1
  unfold thrEnts
  cases hc : clr H e.1
  · rw [Bool.cond_false, List.sum_replicate, smul_eq_mul]
    have hall : ∀ it ∈ thrItems t.TT e, sel H it.1 it.2 (zero8 t.wT t.offT) = zero8 t.wT t.offT := by
      intro it hit
      simp only [thrItems, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hit
      obtain ⟨p, hp, hit⟩ := hit
      have hinc := hf.thrIncl e he p.1 (List.of_mem_zip hp).1
      rw [sel_eq]
      rcases hit with rfl | rfl | rfl
      · rw [clr_incl hinc.1 hc]; rfl
      · rw [clr_incl hinc.2.1 hc]; rfl
      · rw [clr_incl hinc.2.2 hc]; rfl
    rw [sum_const _ _ _ hall]
    congr 1
    simp only [thrItems, List.length_flatMap, List.length_cons, List.length_nil]
    rw [List.map_const', List.sum_replicate, List.length_zip, hlen, hTT]
    norm_num
  · rw [Bool.cond_true, thrL_map]
    rfl

/-- One group of items with the same new part `m`. -/
theorem thr_group (w : ℕ → ℝ) (z m : ℕ) : ∀ (L : List (ℕ × ℕ)),
    (∀ it ∈ L, Nat.shiftRight it.1 105 = m) →
    (L.map fun it => sel (hot (code 8 w)) it.1 it.2 z).sum
      = sel (hotN 35 (ext 7 w)) m
          (sumL (fun it => sel (hotN 35 (code 7 w)) it.1 it.2 z)
            (L.map fun it => (Nat.land it.1 lowM, it.2)))
          (Nat.mul L.length z)
  | [], _ => by simp [sel_eq, sumL, nmul]
  | it :: L, h => by
    have ih := thr_group w z m L fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hit := h it List.mem_cons_self
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, sumL, List.length_cons]
    simp only [sel_eq, clr_hot, hit, nadd, nmul]
    cases clr (hotN 35 (ext 7 w)) m
    · simp only [Bool.and_false, Bool.cond_false]
      ring
    · simp only [Bool.and_true, Bool.cond_true]

theorem thrRun_eq (Hx : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ)) (acc : ℕ),
    thrRun Hx l acc = acc + (l.map fun p => sel Hx p.1 p.2.1 p.2.2).sum
  | [], acc => by simp [thrRun]
  | p :: l, acc => by
    rw [thrRun, thrRun_eq Hx l, List.map_cons, List.sum_cons, nadd]
    ring

theorem thrLive_dead (Hx : ℕ) : ∀ (P : List (ℕ × ℕ × ℕ)),
    thrDead P + ((thrLive P).map fun p => sel Hx p.1 p.2.1 p.2.2).sum
      = (P.map fun p => sel Hx p.1 p.2.1 p.2.2).sum
  | [] => by simp [thrDead, thrLive]
  | p :: P => by
    have ih := thrLive_dead Hx P
    rw [thrDead, thrLive, List.map_cons, List.sum_cons, ← ih]
    cases hb : Nat.beq p.2.1 p.2.2
    · simp only [Bool.cond_false, List.map_cons, List.sum_cons]
      ring
    · have he : p.2.1 = p.2.2 := Nat.eq_of_beq_eq_true hb
      simp only [Bool.cond_true, nadd, sel_eq, he]
      cases clr Hx p.1 <;> simp <;> ring

theorem thrPrep_map (HT z : ℕ) : ∀ (G : List (ℕ × ℕ × List (ℕ × ℕ))),
    thrPrep HT z G = G.map fun g =>
      (g.1, sumL (fun it => sel HT it.1 it.2 z) g.2.2, Nat.mul g.2.1 z)
  | [] => rfl
  | g :: G => by rw [thrPrep, thrPrep_map HT z G, List.map_cons]

include ht hf in
/-- **The threshold sum.** -/
theorem thr_fast :
    thrRun (hotN 35 (ext 7 w))
        (thrLive (thrPrep (hotN 35 (code 7 w)) (zero8 t.wT t.offT) f.thrG))
        (thrDead (thrPrep (hotN 35 (code 7 w)) (zero8 t.wT t.offT) f.thrG))
      = thrAcc t (hot (code 8 w)) (zero8 t.wT t.offT) (Nat.mul 24 (zero8 t.wT t.offT)) t.thr 0 := by
  rw [thr_flat ht hf, thrRun_eq, thrLive_dead, thrPrep_map, hf.thrG, List.map_map, List.map_map,
    regroup (fun it : ℕ × ℕ => Nat.shiftRight it.1 105) _ _ hf.thrNd (thrFlat t) hf.thrK]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_def]
  rw [thr_group w _ m _ fun it hit => Nat.eq_of_beq_eq_true (List.mem_filter.1 hit).2]

/-! ### Objective count -/

include hf in
/-- **The objective count.** -/
theorem obj_fast :
    Nat.add (objCnt (hotN 35 (code 7 w)) f.objO 0) (objCnt (hotN 35 (ext 7 w)) f.objN 0)
      = objCnt (hot (code 8 w)) t.obj 0 := by
  have hA : objCnt (hot (code 8 w)) t.obj 0 = t.obj.countP (clr (hot (code 8 w))) := by
    rw [objCnt_eq, zero_add]
  have hB : objCnt (hotN 35 (code 7 w)) f.objO 0 = f.objO.countP (clr (hotN 35 (code 7 w))) := by
    rw [objCnt_eq, zero_add]
  have hC : objCnt (hotN 35 (ext 7 w)) f.objN 0 = f.objN.countP (clr (hotN 35 (ext 7 w))) := by
    rw [objCnt_eq, zero_add]
  have hsplit := List.countP_eq_countP_filter_add t.obj (clr (hot (code 8 w)))
    (fun m => Nat.beq (Nat.shiftRight m 105) 0)
  have h1 : (t.obj.filter fun m => Nat.beq (Nat.shiftRight m 105) 0).countP (clr (hot (code 8 w)))
      = (t.obj.filter fun m => Nat.beq (Nat.shiftRight m 105) 0).countP
          (clr (hotN 35 (code 7 w))) := by
    apply List.countP_congr
    intro m hm
    have h0 : Nat.shiftRight m 105 = 0 := Nat.eq_of_beq_eq_true (List.mem_filter.1 hm).2
    have hlt : m < 2 ^ 105 := by
      rw [nshr, Nat.shiftRight_eq_div_pow] at h0
      exact (Nat.div_eq_zero_iff_lt (by positivity)).1 h0
    have hm' : Nat.land m lowM = m := by
      rw [nland, lowM, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
    rw [clr_hot, h0, hm', clr_zero, Bool.and_true]
  have h2 : (t.obj.filter fun m => !(Nat.beq (Nat.shiftRight m 105) 0)).countP
        (clr (hot (code 8 w)))
      = (t.obj.filter fun m => !(Nat.beq (Nat.shiftRight m 105) 0)).countP
          ((clr (hotN 35 (ext 7 w))) ∘ fun m => Nat.shiftRight m 105) := by
    apply List.countP_congr
    intro m hm
    obtain ⟨hmem, hne⟩ := List.mem_filter.1 hm
    have hz : Nat.land m lowM = 0 := by
      rcases hf.objSh m hmem with h | h
      · rw [h] at hne; simp at hne
      · exact h
    simp only [Function.comp_apply]
    rw [clr_hot, hz, clr_zero, Bool.true_and]
  rw [hA, hB, hC, nadd, hf.objO, hf.objN, List.countP_map, hsplit, h1, h2]

include ht hf in
/-- **The specialised evaluation agrees with the plain one** on the packed pattern of a sample. -/
theorem lamUVF_eq : lamUVF t f (code 7 w) (ext 7 w) = lamUV t (code 8 w) := by
  have hsub := hf.psok
  rw [ht.sub5] at hsub
  have hC : Nat.add (codes (code 7 w) t.sub5) (codesX (ext 7 w) f.sNew) = codes (code 8 w) t.sub5 := by
    rw [hf.sNew, ht.sub5]
    exact codes_fast w hsub
  simp only [lamUVF, lamUV, hC, sq_fast ht hf w, deg_fast ht hf w, thr_fast ht hf w,
    obj_fast hf w]

include ht hf in
theorem leafOkF_eq (p q e : ℤ) :
    leafOkF t f p q e (code 7 w) (ext 7 w) = leafOk t p q e (code 8 w) := by
  simp only [leafOkF, leafOk, lamUVF_eq ht hf w]

end Fast

end BeatAvg.K8
