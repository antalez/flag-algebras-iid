import BeatAvg.Six.Data
import BeatAvg.Cert.Levels

/-!
# The patterns of six points

`D.L6` contains the pattern of every sorted sample of six points in general position.

The search assigns the trits of the fifteen quadruples one after another (`ord6`) and abandons a
prefix as soon as it determines the pattern of five of the points and that pattern is not in
`D.L5`. A complete assignment is dropped only with a valid certificate of non-realizability. The
kernel runs the search and compares its result with `D.L6`.
-/

namespace BeatAvg.Six

/-! ### Certificates of non-realizability -/

/-- Code of a pattern: `∑ v[i] 3^i`. -/
def codeL (v : List ℕ) : ℕ := v.foldr (fun x acc => acc * 3 + x) 0

/-- The pattern `v` on `n` points carries a valid certificate of non-realizability. -/
def excl (certs : List (ℕ × Fast.Cert)) (n : ℕ) (v : List ℕ) : Bool :=
  match certs.lookup (codeL v) with
  | some cert => Fast.farkasOk (Fast.combos n) n v.toArray cert
  | none => false

theorem excl_false (certs : List (ℕ × Fast.Cert)) {n : ℕ} {w : ℕ → ℝ} (hw : SG n w) :
    excl certs n ((Fast.combos n).map (trit w)) = false := by
  unfold excl
  split
  · rename_i cert _
    cases hc : Fast.farkasOk (Fast.combos n) n ((Fast.combos n).map (trit w)).toArray cert
    · rfl
    · exact (farkas_sound hw cert hc).elim
  · rfl

theorem trit_le_two (w : ℕ → ℝ) (q : ℕ × ℕ × ℕ × ℕ) : trit w q ≤ 2 := by
  unfold trit; split_ifs <;> omega

/-! ### Five points -/

/-- All lists of `n` trits. -/
def allTrits : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (allTrits n).flatMap fun v => [0 :: v, 1 :: v, 2 :: v]

theorem mem_allTrits : ∀ v : List ℕ, (∀ x ∈ v, x ≤ 2) → v ∈ allTrits v.length := by
  intro v
  induction v with
  | nil => intro _; simp [allTrits]
  | cons x v ih =>
    intro h
    have hx : x ≤ 2 := h x List.mem_cons_self
    have hv := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.length_cons, allTrits, List.mem_flatMap]
    refine ⟨v, hv, ?_⟩
    interval_cases x <;> simp

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
/-- Every list of five trits is in `D.L5` or carries a certificate. -/
theorem check5 : ((allTrits 5).all fun v => D.L5.contains v || excl D.certs5 5 v) = true := by
  decide +kernel

/-- `D.L5` contains the pattern of every sorted sample of five points in general position. -/
theorem cover5 {w : ℕ → ℝ} (hw : SG 5 w) : (Fast.combos 5).map (trit w) ∈ D.L5 := by
  have hlen : ((Fast.combos 5).map (trit w)).length = 5 := by
    rw [List.length_map]; decide
  have hmem : (Fast.combos 5).map (trit w) ∈ allTrits 5 := by
    rw [← hlen]
    apply mem_allTrits
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    exact trit_le_two w q
  have h := List.all_eq_true.1 check5 _ hmem
  rw [excl_false D.certs5 hw, Bool.or_false] at h
  exact List.contains_iff_mem.1 h

/-! ### Six points -/

/-- The order in which the quadruples are decided: the subset `{0,..,4}` first, then the subsets
missing `4`, `3`, `2`, `1` and `0` are completed one after another. -/
def ord6 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4), (0, 1, 2, 5),
   (0, 1, 3, 5), (0, 2, 3, 5), (1, 2, 3, 5), (0, 1, 4, 5), (0, 2, 4, 5), (1, 2, 4, 5),
   (0, 3, 4, 5), (1, 3, 4, 5), (2, 3, 4, 5)]

/-- Positions, in `ord6`, of the quadruples of the five points other than `d`. -/
def restrPos (d : ℕ) : List ℕ := (Fast.combos 5).map fun q => ord6.idxOf (Fast.skipQ d q)

/-- Length of the prefix that decides the pattern of the five points other than `d`. -/
def need : List ℕ := [15, 15, 14, 12, 9, 5]

/-- The prefix has just decided a five-point pattern that is not in `D.L5`. -/
def prune (acc : List ℕ) : Bool :=
  (List.range 6).any fun d =>
    need.getD d 0 == acc.length && !(D.L5.contains ((restrPos d).map fun p => acc.getD p 0))

/-- The complete assignments below `acc` that are not abandoned. -/
def dfs : ℕ → List ℕ → List (List ℕ)
  | 0, acc => if prune acc then [] else [acc]
  | r + 1, acc =>
    if prune acc then [] else dfs r (acc ++ [0]) ++ dfs r (acc ++ [1]) ++ dfs r (acc ++ [2])

/-- From the order of the search to the order of `Fast.combos 6`. -/
def toC (v : List ℕ) : List ℕ := (Fast.combos 6).map fun q => v.getD (ord6.idxOf q) 0

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
/-- The search returns `D.L6` and patterns with a certificate. -/
theorem check6 :
    (((dfs 15 []).map toC).filter fun v => !(excl D.certs6 6 v)) = D.L6 := by
  decide +kernel

theorem dfs_complete : ∀ (r : ℕ) (acc rest : List ℕ), rest.length = r → (∀ x ∈ rest, x ≤ 2) →
    (∀ k, acc.length ≤ k → k ≤ (acc ++ rest).length → prune ((acc ++ rest).take k) = false) →
    acc ++ rest ∈ dfs r acc := by
  intro r
  induction r with
  | zero =>
    intro acc rest hlen _ hp
    have hr : rest = [] := List.length_eq_zero_iff.1 hlen
    subst hr
    have h := hp acc.length le_rfl (by simp)
    simp only [List.append_nil, List.take_length] at h
    simp [dfs, h]
  | succ r ih =>
    intro acc rest hlen h2 hp
    obtain ⟨x, rest', rfl⟩ : ∃ x rest', rest = x :: rest' := by
      cases rest with
      | nil => simp at hlen
      | cons x t => exact ⟨x, t, rfl⟩
    have hacc : prune acc = false := by
      have h := hp acc.length le_rfl (by simp)
      rwa [List.take_left'] at h
      rfl
    have hx : x ≤ 2 := h2 x List.mem_cons_self
    have hrec : (acc ++ [x]) ++ rest' ∈ dfs r (acc ++ [x]) := by
      apply ih (acc ++ [x]) rest' (by simpa using hlen)
        (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
      intro k hk1 hk2
      have e : (acc ++ [x]) ++ rest' = acc ++ x :: rest' := by simp
      rw [e] at hk2 ⊢
      exact hp k (by simp at hk1; omega) hk2
    have e : acc ++ x :: rest' = (acc ++ [x]) ++ rest' := by simp
    rw [e]
    simp only [dfs, hacc, Bool.false_eq_true, if_false, List.mem_append]
    interval_cases x
    · exact Or.inl (Or.inl hrec)
    · exact Or.inl (Or.inr hrec)
    · exact Or.inr hrec

theorem ord6_length : ord6.length = 15 := by decide

theorem mem_ord6 : ∀ q ∈ Fast.combos 6, q ∈ ord6 := by decide

theorem restrPos_lt : ∀ d < 6, ∀ p ∈ restrPos d, p < need.getD d 0 := by decide

theorem getD_map_idxOf (f : ℕ × ℕ × ℕ × ℕ → ℕ) {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ ord6) :
    (ord6.map f).getD (ord6.idxOf q) 0 = f q := by
  have hi : ord6.idxOf q < ord6.length := List.idxOf_lt_length_iff.2 hq
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_idxOf hi]

/-- The pattern of a sample, in the order of the search, is never abandoned. -/
theorem prune_false {w : ℕ → ℝ} (hw : SG 6 w) (k : ℕ) :
    prune ((ord6.map (trit w)).take k) = false := by
  unfold prune
  rw [List.any_eq_false]
  intro d hd
  have hd6 : d < 6 := List.mem_range.1 hd
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', not_and, Bool.not_eq_false]
  intro hneed
  have hrestr : ((restrPos d).map fun p => ((ord6.map (trit w)).take k).getD p 0)
      = (Fast.combos 5).map (trit (w ∘ Fast.skip d)) := by
    unfold restrPos
    rw [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp_apply]
    have hmem : Fast.skipQ d q ∈ ord6 := mem_ord6 _ (skipQ_mem (n := 6) (by norm_num) d hq)
    have hp : ord6.idxOf (Fast.skipQ d q) < need.getD d 0 :=
      restrPos_lt d hd6 _ (List.mem_map_of_mem (f := fun q => ord6.idxOf (Fast.skipQ d q)) hq)
    have hp' : ord6.idxOf (Fast.skipQ d q) < ((ord6.map (trit w)).take k).length := by
      rw [← hneed]; exact hp
    have hk : ord6.idxOf (Fast.skipQ d q) < k := by
      rw [List.length_take] at hp'; omega
    rw [List.getD_eq_getElem _ _ hp', List.getElem_take,
      ← List.getD_eq_getElem (d := 0), getD_map_idxOf _ hmem]
    rfl
  rw [hrestr]
  exact List.contains_iff_mem.2 (cover5 (SG_skip (n := 6) (by norm_num) hw d))

/-- **Completeness.** `D.L6` contains the pattern of every sorted sample of six points in
general position. -/
theorem cover6 {w : ℕ → ℝ} (hw : SG 6 w) : (Fast.combos 6).map (trit w) ∈ D.L6 := by
  have h1 : [] ++ ord6.map (trit w) ∈ dfs 15 [] := by
    apply dfs_complete 15 [] (ord6.map (trit w)) (by rw [List.length_map, ord6_length])
    · intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact trit_le_two w q
    · intro k _ _
      rw [List.nil_append]
      exact prune_false hw k
  rw [List.nil_append] at h1
  have h2 : toC (ord6.map (trit w)) = (Fast.combos 6).map (trit w) := by
    unfold toC
    exact List.map_congr_left fun q hq => getD_map_idxOf _ (mem_ord6 q hq)
  rw [← check6, List.mem_filter]
  refine ⟨?_, by rw [excl_false D.certs6 hw]; rfl⟩
  rw [← h2]
  exact List.mem_map_of_mem h1

end BeatAvg.Six
