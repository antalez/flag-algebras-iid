import BeatAvg.Cert.Levels
import BeatAvg.K8.Bits

/-!
# Completeness of the kernel-friendly enumeration

If the grouped level `G` of `m` points contains the pattern of every sample, then the extension of
the pattern of any sample of `m + 1` points is found by the join of `Search.lean`.
-/

namespace BeatAvg.K8

open BeatAvg

/-- The pattern of a sample, in nested order. -/
noncomputable def pat (n : ℕ) (w : ℕ → ℝ) : List ℕ := (ordQ n).map (trit w)

/-- The trits of the quadruples whose largest point is `m`. -/
noncomputable def extL (m : ℕ) (w : ℕ → ℝ) : List ℕ :=
  (triples m).map fun t => trit w (t.1, t.2.1, t.2.2, m)

noncomputable def code (n : ℕ) (w : ℕ → ℝ) : ℕ := packL (pat n w)

noncomputable def ext (m : ℕ) (w : ℕ → ℝ) : ℕ := packL (extL m w)

theorem trit_lt_four (w : ℕ → ℝ) (q : ℕ × ℕ × ℕ × ℕ) : trit w q < 4 := by
  unfold trit; split_ifs <;> omega

theorem trit_le_two (w : ℕ → ℝ) (q : ℕ × ℕ × ℕ × ℕ) : trit w q ≤ 2 := by
  unfold trit; split_ifs <;> omega

theorem pat_small (n : ℕ) (w : ℕ → ℝ) : Small (pat n w) := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  exact trit_lt_four w q

theorem extL_small (m : ℕ) (w : ℕ → ℝ) : Small (extL m w) := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  exact trit_lt_four w _

theorem pat_succ (m : ℕ) (w : ℕ → ℝ) : pat (m + 1) w = pat m w ++ extL m w := by
  simp only [pat, extL, ordQ, List.map_append, List.map_map]
  rfl

theorem code_succ (m : ℕ) (w : ℕ → ℝ) :
    code (m + 1) w = code m w + 4 ^ (ordQ m).length * ext m w := by
  rw [code, pat_succ, packL_append]
  simp only [code, ext, pat, List.length_map]

/-- The grouped level `G` (patterns of `m + 1` points, keyed by the pattern of the first `m`,
extensions of `wb` bits) contains the pattern of every sample. -/
def LevelOk (G : Grouped) (wb m : ℕ) : Prop :=
  ∀ w, SG (m + 1) w → ext m w ∈ unpackE wb (lookupG G (code m w)).1 (lookupG G (code m w)).2

def skipT (j : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (Fast.skip j t.1, Fast.skip j t.2.1, Fast.skip j t.2.2)

/-- Mask of the trits assigned after the stages `j, ..., j + f - 1`. -/
def accMask (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, A => A
  | f + 1, j, A => accMask m f (j + 1) (Nat.lor A (maskM (avoidT m j)))

/-- The facts about the orders used by the proof, for restrictions of `m + 1` points. -/
def statOk (m : ℕ) : Bool :=
  ((List.range (m + 1)).all fun j =>
      (ordQ m).map (Fast.skipQ j) == (ordQ (m + 1)).filter (avoid4 j) &&
      (triples m).map (skipT j) == (triples (m + 1)).filter (avoid3 j)) &&
    accMask (m + 1) m 1 (maskM (avoidT (m + 1) 0)) == 4 ^ (triples (m + 1)).length - 1

theorem ext1_mem {O V e : ℕ} : ∀ {E : List ℕ}, e ∈ E → (e ^^^ V) &&& O = 0 → V ||| e ∈ ext1 O V E
  | [], h, _ => by simp at h
  | a :: E, h, ht => by
    rw [List.mem_cons] at h
    by_cases ha : Nat.beq (Nat.land (Nat.xor a V) O) 0 = true
    · simp only [ext1, ha, Bool.cond_true, List.mem_cons]
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ext1_mem h ht)
    · simp only [ext1, ha, Bool.cond_false]
      rcases h with rfl | h
      · exact absurd (by rw [nland, nxor, ht]; rfl) ha
      · exact ext1_mem h ht

theorem extAll_mem {O V e : ℕ} {E : List ℕ} (he : e ∈ E) (ht : (e ^^^ V) &&& O = 0) :
    ∀ {st : List ℕ}, V ∈ st → V ||| e ∈ extAll O E st
  | [], h => by simp at h
  | a :: st, h => by
    rw [List.mem_cons] at h
    simp only [extAll, List.mem_append]
    rcases h with rfl | h
    · exact Or.inl (ext1_mem he ht)
    · exact Or.inr (extAll_mem he ht h)

theorem extAll_append (O : ℕ) (E : List ℕ) : ∀ (a b : List ℕ),
    extAll O E (a ++ b) = extAll O E a ++ extAll O E b
  | [], b => rfl
  | x :: a, b => by simp only [List.cons_append, extAll, extAll_append O E a b, List.append_assoc]

theorem joinFrom_append (G : Grouped) (wb m T : ℕ) : ∀ (f j A : ℕ) (a b : List ℕ),
    joinFrom G wb m T f j A (a ++ b) = joinFrom G wb m T f j A a ++ joinFrom G wb m T f j A b
  | 0, _, _, _, _ => rfl
  | f + 1, j, A, a, b => by
    simp only [joinFrom, extAll_append, joinFrom_append G wb m T f]

theorem joinFrom_mem (G : Grouped) (wb m T x : ℕ) : ∀ (f j A : ℕ) (st : List ℕ), x &&& A ∈ st →
    (∀ j', j ≤ j' → j' < j + f → x &&& maskM (avoidT m j') ∈ candsJ G wb m T j') →
    x &&& accMask m f j A ∈ joinFrom G wb m T f j A st
  | 0, _, _, _, h, _ => h
  | f + 1, j, A, st, h, hc => by
    simp only [joinFrom, accMask]
    apply joinFrom_mem G wb m T x f (j + 1)
    · have h1 := extAll_mem (O := Nat.land A (maskM (avoidT m j))) (hc j le_rfl (by omega))
        (compat_test x A (maskM (avoidT m j))) h
      rwa [lor_land] at h1
    · intro j' h1 h2
      exact hc j' (by omega) (by omega)

/-- The stages after the first, from the states `st`. -/
def extsFrom (G : Grouped) (wb m T : ℕ) (st : List ℕ) : List ℕ :=
  joinFrom G wb m T (m - 1) 1 (maskM (avoidT m 0)) st

theorem extsR_eq (G : Grouped) (wb m T lo hi : ℕ) :
    extsR G wb m T lo hi = extsFrom G wb m T (((candsJ G wb m T 0).drop lo).take (hi - lo)) := rfl

theorem extsFrom_append (G : Grouped) (wb m T : ℕ) (a b : List ℕ) :
    extsFrom G wb m T (a ++ b) = extsFrom G wb m T a ++ extsFrom G wb m T b :=
  joinFrom_append G wb m T _ _ _ a b

section Restr

variable {m : ℕ} {w : ℕ → ℝ}

theorem skip_top {j : ℕ} (hj : j < m + 1) : Fast.skip j m = m + 1 := by
  unfold Fast.skip
  rw [ite_eq_right (by omega : ¬ m < j)]

/-- The code of the restriction that deletes the point `j`. -/
theorem code_skip (hs : statOk m = true) {j : ℕ} (hj : j < m + 1) :
    code m (w ∘ Fast.skip j) = gatherM (avoidQ (m + 1) j) (code (m + 1) w) := by
  simp only [statOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hs
  have h1 := (hs.1 j hj).1
  have hl : (avoidQ (m + 1) j).length = (pat (m + 1) w).length := by simp [avoidQ, pat]
  rw [code, code, gatherM_packL _ _ (pat_small _ w) hl]
  simp only [avoidQ, pat]
  rw [pick_map, ← h1, List.map_map]
  rfl

theorem ext_skip (hs : statOk m = true) {j : ℕ} (hj : j < m + 1) :
    ext m (w ∘ Fast.skip j) = gatherM (avoidT (m + 1) j) (ext (m + 1) w) := by
  simp only [statOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hs
  have h2 := (hs.1 j hj).2
  have hl : (avoidT (m + 1) j).length = (extL (m + 1) w).length := by simp [avoidT, extL]
  rw [ext, ext, gatherM_packL _ _ (extL_small _ w) hl]
  simp only [avoidT, extL]
  rw [pick_map, ← h2, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, skipT]
  rw [← skip_top hj]
  rfl

/-- **Completeness of the join.** -/
theorem exts_complete {G : Grouped} {wb : ℕ} (hG : LevelOk G wb m) (hs : statOk m = true)
    (hw : SG (m + 2) w) :
    ext (m + 1) w ∈ extsFrom G wb (m + 1) (code (m + 1) w)
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
  have h := joinFrom_mem G wb (m + 1) (code (m + 1) w) (ext (m + 1) w) m 1
    (maskM (avoidT (m + 1) 0)) _ (hc 0 (by omega)) (fun j' _ h2 => hc j' (by omega))
  rw [hfin] at h
  have e4 : (4 : ℕ) ^ (triples (m + 1)).length = 2 ^ (2 * (triples (m + 1)).length) := by
    rw [pow_mul]; norm_num
  rw [e4, Nat.and_two_pow_sub_one_eq_mod, ← e4, Nat.mod_eq_of_lt hx] at h
  exact h

end Restr

end BeatAvg.K8
