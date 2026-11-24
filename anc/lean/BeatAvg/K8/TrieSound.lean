import BeatAvg.K8.SearchSound

/-!
# Completeness of the join with tries
-/

namespace BeatAvg.K8

open BeatAvg

theorem tr_eq (N k : ℕ) : tr N k = N / 2 ^ (2 * k) % 2 ^ 2 := by
  simp only [tr, nmod, nshr, nmul, Nat.shiftRight_eq_div_pow]
  rfl

theorem testBit_tr (N k i : ℕ) : (tr N k).testBit i = (decide (i < 2) && N.testBit (2 * k + i)) := by
  rw [tr_eq, Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem tr_land (a b k : ℕ) : tr (a &&& b) k = tr a k &&& tr b k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_tr, Nat.testBit_and]
  cases decide (i < 2) <;> simp

theorem tr_lor (a b k : ℕ) : tr (a ||| b) k = tr a k ||| tr b k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_tr, Nat.testBit_or]
  cases decide (i < 2) <;> simp

theorem tr_lt (N k : ℕ) : tr N k < 4 := by rw [tr_eq]; exact Nat.mod_lt _ (by norm_num)

/-- A mask of whole trits. -/
def TMask (A : ℕ) : Prop := ∀ k, tr A k = 0 ∨ tr A k = 3

theorem TMask.lor {a b : ℕ} (ha : TMask a) (hb : TMask b) : TMask (a ||| b) := by
  intro k
  rw [tr_lor]
  rcases ha k with h1 | h1 <;> rcases hb k with h2 | h2 <;> rw [h1, h2] <;> decide

theorem tr_zero (k : ℕ) : tr 0 k = 0 := by rw [tr_eq]; simp

theorem tr_four_mul_succ (a b k : ℕ) (hb : b < 4) : tr (b + 4 * a) (k + 1) = tr a k := by
  rw [tr_eq, tr_eq]
  congr 1
  have e : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by rw [Nat.mul_succ, pow_add]; ring
  rw [e, ← Nat.div_div_eq_div_mul]
  congr 1
  omega

theorem tr_four_mul_zero (a b : ℕ) (hb : b < 4) : tr (b + 4 * a) 0 = b := by
  rw [tr_eq]; simp; omega

theorem maskM_tmask : ∀ bs : List Bool, TMask (maskM bs)
  | [] => fun k => Or.inl (tr_zero k)
  | b :: bs => by
    intro k
    cases b
    · have e : maskM (false :: bs) = 0 + 4 * maskM bs := by simp [maskM]
      rw [e]
      cases k with
      | zero => rw [tr_four_mul_zero _ _ (by norm_num)]; exact Or.inl rfl
      | succ k => rw [tr_four_mul_succ _ _ _ (by norm_num)]; exact maskM_tmask bs k
    · have e : maskM (true :: bs) = 3 + 4 * maskM bs := rfl
      rw [e]
      cases k with
      | zero => rw [tr_four_mul_zero _ _ (by norm_num)]; exact Or.inr rfl
      | succ k => rw [tr_four_mul_succ _ _ _ (by norm_num)]; exact maskM_tmask bs k

/-! ### Tries -/

theorem withTrit_mem {p t e : ℕ} : ∀ {E : List ℕ}, e ∈ E → tr e p = t → e ∈ withTrit p t E
  | [], h, _ => by simp at h
  | a :: E, h, ht => by
    rw [List.mem_cons] at h
    unfold withTrit
    cases hb : Nat.beq (tr a p) t
    · rw [Bool.cond_false]
      rcases h with rfl | h
      · rw [ht, Nat.beq_refl] at hb; exact absurd hb (by simp)
      · exact withTrit_mem h ht
    · rw [Bool.cond_true, List.mem_cons]
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (withTrit_mem h ht)

theorem trieFind_build : ∀ (ps E : List ℕ) (e V : ℕ), e ∈ E → (∀ p ∈ ps, tr e p ≤ 2) →
    (∀ p ∈ ps, tr V p = tr e p) → e ∈ trieFind (trieBuild ps E) ps V
  | [], E, e, V, he, _, _ => he
  | p :: ps, E, e, V, he, h2, hV => by
    have hp := h2 p List.mem_cons_self
    have hvp := hV p List.mem_cons_self
    have h2' : ∀ q ∈ ps, tr e q ≤ 2 := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
    have hV' : ∀ q ∈ ps, tr V q = tr e q := fun q hq => hV q (List.mem_cons_of_mem _ hq)
    unfold trieBuild trieFind
    rw [hvp]
    have : tr e p = 0 ∨ tr e p = 1 ∨ tr e p = 2 := by omega
    rcases this with h | h | h
    · rw [h]
      exact trieFind_build ps _ e V (withTrit_mem he h) h2' hV'
    · rw [h]
      exact trieFind_build ps _ e V (withTrit_mem he h) h2' hV'
    · rw [h]
      exact trieFind_build ps _ e V (withTrit_mem he h) h2' hV'

theorem extAllT_mem {t : Trie} {ps : List ℕ} {V e : ℕ} (he : e ∈ trieFind t ps V) :
    ∀ {st : List ℕ}, V ∈ st → V ||| e ∈ extAllT t ps st
  | [], h => by simp at h
  | a :: st, h => by
    rw [List.mem_cons] at h
    simp only [extAllT, List.mem_append]
    rcases h with rfl | h
    · exact Or.inl (List.mem_map_of_mem he)
    · exact Or.inr (extAllT_mem he h)

theorem mem_ovl {k A M p : ℕ} (h : p ∈ ovl k A M) : tr A p = 3 ∧ tr M p = 3 ∨ tr (A &&& M) p ≠ 0 := by
  right
  unfold ovl at h
  rw [List.mem_filter] at h
  have h2 := h.2
  simp only [Bool.not_eq_true'] at h2
  intro hc
  rw [nland, hc, Nat.beq_refl] at h2
  exact absurd h2 (by simp)

/-- One stage of the join with a trie. -/
theorem stage_mem {x A M : ℕ} {E : List ℕ} (k : ℕ) (hx : ∀ p, tr x p ≤ 2) (hA : TMask A) (hM : TMask M)
    {st : List ℕ} (hst : x &&& A ∈ st) (hE : x &&& M ∈ E) :
    x &&& (A ||| M) ∈ extAllT (trieBuild (ovl k A M) E) (ovl k A M) st := by
  rw [← lor_land]
  apply extAllT_mem _ hst
  apply trieFind_build _ _ _ _ hE
  · intro p _
    rw [tr_land]
    exact le_trans Nat.and_le_left (hx p)
  · intro p hp
    rcases mem_ovl hp with ⟨h1, h2⟩ | h
    · rw [tr_land, tr_land, h1, h2]
    · rw [tr_land] at h
      have h1 : tr A p = 3 := by
        rcases hA p with h1 | h1
        · rw [h1] at h; simp at h
        · exact h1
      have h2 : tr M p = 3 := by
        rcases hM p with h2 | h2
        · rw [h2] at h; simp at h
        · exact h2
      rw [tr_land, tr_land, h1, h2]

theorem joinFromT_mem (G : Grouped) (wb m T x : ℕ) (hx : ∀ p, tr x p ≤ 2) : ∀ (f j A : ℕ) (st : List ℕ),
    TMask A → x &&& A ∈ st →
    (∀ j', j ≤ j' → j' < j + f → x &&& maskM (avoidT m j') ∈ candsJ G wb m T j') →
    x &&& accMask m f j A ∈ joinFromT G wb m T f j A st
  | 0, _, _, _, _, h, _ => h
  | f + 1, j, A, st, hA, h, hc => by
    simp only [joinFromT, accMask]
    apply joinFromT_mem G wb m T x hx f (j + 1)
    · exact hA.lor (maskM_tmask _)
    · rw [nlor]
      exact stage_mem _ hx hA (maskM_tmask _) h (hc j le_rfl (by omega))
    · intro j' h1 h2
      exact hc j' (by omega) (by omega)

theorem joinFromT_append (G : Grouped) (wb m T : ℕ) : ∀ (f j A : ℕ) (a b : List ℕ),
    joinFromT G wb m T f j A (a ++ b) = joinFromT G wb m T f j A a ++ joinFromT G wb m T f j A b := by
  intro f
  induction f with
  | zero => intro _ _ _ _; rfl
  | succ f ih =>
    intro j A a b
    simp only [joinFromT]
    rw [← ih]
    congr 1
    induction a with
    | nil => rfl
    | cons v a iha => simp only [List.cons_append, extAllT, iha, List.append_assoc]

end BeatAvg.K8

namespace BeatAvg.K8

open BeatAvg

theorem tr_ext_le (m : ℕ) (w : ℕ → ℝ) (p : ℕ) : tr (ext m w) p ≤ 2 := by
  rw [ext, tr_packL _ _ (extL_small m w)]
  by_cases hp : p < (extL m w).length
  · rw [List.getD_eq_getElem _ _ hp]
    obtain ⟨q, -, hq⟩ := List.mem_map.1 (List.getElem_mem hp)
    rw [← hq]
    unfold trit; split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by omega)]; omega

/-- **Completeness of the join with tries.** -/
theorem exts_completeT {m : ℕ} {w : ℕ → ℝ} {G : Grouped} {wb : ℕ} (hG : LevelOk G wb m)
    (hs : statOk m = true) (hw : SG (m + 2) w) :
    ext (m + 1) w ∈ joinFromT G wb (m + 1) (code (m + 1) w) m 1 (maskM (avoidT (m + 1) 0))
      (candsJ G wb (m + 1) (code (m + 1) w) 0) := by
  have hc : ∀ j, j < m + 1 → ext (m + 1) w &&& maskM (avoidT (m + 1) j)
      ∈ candsJ G wb (m + 1) (code (m + 1) w) j := by
    intro j hj
    have hsk : SG (m + 1) (w ∘ Fast.skip j) := SG_skip (n := m + 2) (by omega) hw j
    have h := hG _ hsk
    rw [code_skip hs hj, ext_skip hs hj] at h
    have hl : (avoidT (m + 1) j).length = (extL (m + 1) w).length := by simp [avoidT, extL]
    rw [ext, ← spread_gather _ _ (extL_small _ w) hl]
    exact List.mem_map_of_mem h
  have hx : ext (m + 1) w < 4 ^ (triples (m + 1)).length := by
    have := packL_lt (extL_small (m + 1) w)
    simpa [ext, extL] using this
  have hfin : accMask (m + 1) m 1 (maskM (avoidT (m + 1) 0)) = 4 ^ (triples (m + 1)).length - 1 := by
    simp only [statOk, Bool.and_eq_true, beq_iff_eq] at hs
    exact hs.2
  have h := joinFromT_mem G wb (m + 1) (code (m + 1) w) (ext (m + 1) w) (tr_ext_le _ w) m 1
    (maskM (avoidT (m + 1) 0)) _ (maskM_tmask _) (hc 0 (by omega)) (fun j' _ h2 => hc j' (by omega))
  rw [hfin] at h
  have e4 : (4 : ℕ) ^ (triples (m + 1)).length = 2 ^ (2 * (triples (m + 1)).length) := by
    rw [pow_mul]; norm_num
  rw [e4, Nat.and_two_pow_sub_one_eq_mod, ← e4, Nat.mod_eq_of_lt hx] at h
  exact h

end BeatAvg.K8
