import BeatAvg.Cert.CoverSpec

/-!
# The level built by `Fast.mkLevel` satisfies its specification

This is a property of the program `mkLevel`, proved for every list `R`. The only finite fact is that
every quadruple of `n` points misses one of the points (`covOk n`), checked by the kernel.
-/

namespace BeatAvg

/-- Every position of the `n`-point pattern lies in the position map of some stage, and position
maps only contain positions. -/
def covOk (n : ℕ) : Bool :=
  ((List.range (Fast.combos n).length).all fun pos =>
    (List.range n).any fun j => (Fast.pmOf n (n - 1 - j)).toList.contains pos) &&
  (List.range n).all fun j =>
    (Fast.pmOf n (n - 1 - j)).toList.all fun x => decide (x < (Fast.combos n).length)

theorem cov5 : covOk 5 = true := by decide +kernel
theorem cov6 : covOk 6 = true := by decide +kernel
theorem cov7 : covOk 7 = true := by decide +kernel
theorem cov8 : covOk 8 = true := by decide +kernel

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (h : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_of_lt {α : Type} (a : Array α) (d : α) {i : ℕ} (h : i < a.size) :
    a.getD i d = a[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- `findSrc` finds a stage and an entry holding `pos`, if some stage has it. -/
theorem findSrc_spec (pms : Array (Array ℕ)) (pos : ℕ)
    (h : ∃ j, ∃ hj : j < pms.size, pos ∈ pms[j]) :
    (Fast.findSrc pms pos).1 < pms.size ∧
      (Fast.findSrc pms pos).2 < (pms.getD (Fast.findSrc pms pos).1 #[]).size ∧
      (pms.getD (Fast.findSrc pms pos).1 #[]).getD (Fast.findSrc pms pos).2 0 = pos := by
  obtain ⟨j, hj, hmem⟩ := h
  unfold Fast.findSrc
  cases hf : pms.findIdx? (fun pm => pm.contains pos) with
  | none =>
    rw [Array.findIdx?_eq_none_iff] at hf
    have := hf pms[j] (Array.getElem_mem hj)
    have hc := Array.contains_iff_mem.2 hmem
    rw [this] at hc
    cases hc
  | some i =>
    obtain ⟨hi, hc, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hf
    have hc' : pos ∈ pms[i] := Array.contains_iff_mem.1 hc
    simp only [Option.getD_some]
    rw [getD_of_lt pms #[] hi, Array.idxOf?_eq_map_finIdxOf?_val]
    cases hk : pms[i].finIdxOf? pos with
    | none =>
      rw [Array.finIdxOf?_eq_none_iff] at hk
      exact absurd hc' hk
    | some k =>
      obtain ⟨hk1, -⟩ := Array.finIdxOf?_eq_some_iff.1 hk
      simp only [Option.map_some, Option.getD_some]
      exact ⟨hi, k.isLt, by rw [getD_of_lt _ _ k.isLt]; exact hk1⟩

/-- Position maps of the stages. -/
def pmsOf (n : ℕ) : Array (Array ℕ) := Array.ofFn (n := n) fun j => Fast.pmOf n (n - 1 - j.val)

def srcOf (n : ℕ) : Array (ℕ × ℕ) :=
  Array.ofFn (n := (Fast.combos n).length) fun pos => Fast.findSrc (pmsOf n) pos.val

def oldsOf (n s : ℕ) : Array (ℕ × ℕ × ℕ) :=
  (List.range ((pmsOf n).getD s #[]).size).toArray.filterMap fun k =>
    let jk := (srcOf n).getD (((pmsOf n).getD s #[]).getD k 0) (0, 0)
    if jk.1 < s then some (k, jk.1, jk.2) else none

theorem mkLevel_stages (n : ℕ) (R : Array Fast.Pat) :
    (Fast.mkLevel n R).stages = Array.ofFn (n := n) fun s =>
      ⟨(pmsOf n).getD s.val #[], oldsOf n s.val, Fast.mkBuckets (oldsOf n s.val) R⟩ := rfl

theorem mkLevel_src (n : ℕ) (R : Array Fast.Pat) : (Fast.mkLevel n R).src = srcOf n := rfl

theorem pmsOf_getD {n s : ℕ} (hs : s < n) : (pmsOf n).getD s #[] = Fast.pmOf n (n - 1 - s) :=
  getD_ofFn _ _ hs

theorem stage_getD {n s : ℕ} (hs : s < n) (R : Array Fast.Pat) :
    (Fast.mkLevel n R).stages.getD s dS
      = ⟨Fast.pmOf n (n - 1 - s), oldsOf n s, Fast.mkBuckets (oldsOf n s) R⟩ := by
  rw [mkLevel_stages, getD_ofFn _ _ hs, pmsOf_getD hs]

/-! ### Buckets -/

/-- Bucket key of a pattern. -/
def keyOf (olds : Array (ℕ × ℕ × ℕ)) (T : Fast.Pat) : ℕ :=
  olds.toList.foldl (fun acc o => (acc * 3 + T.getD o.1 0) % Fast.nBuckets) 0

theorem nBuckets_pos : 0 < Fast.nBuckets := by unfold Fast.nBuckets; norm_num

theorem key_lt (l : List (ℕ × ℕ × ℕ)) (T : Fast.Pat) :
    ∀ acc, acc < Fast.nBuckets →
      l.foldl (fun acc o => (acc * 3 + T.getD o.1 0) % Fast.nBuckets) acc < Fast.nBuckets := by
  induction l with
  | nil => intro acc h; exact h
  | cons o t ih => intro acc _; exact ih _ (Nat.mod_lt _ nBuckets_pos)

theorem keyOf_lt (olds : Array (ℕ × ℕ × ℕ)) (T : Fast.Pat) : keyOf olds T < Fast.nBuckets :=
  key_lt _ T 0 nBuckets_pos

theorem buckets_fold (olds : Array (ℕ × ℕ × ℕ)) (l : List Fast.Pat) :
    ∀ tab : Array (Array Fast.Pat), tab.size = Fast.nBuckets → ∀ T,
      (T ∈ l ∨ T ∈ (tab.getD (keyOf olds T) #[]).toList) →
      T ∈ ((l.foldl (fun tab T => tab.modify (keyOf olds T) (·.push T)) tab).getD
        (keyOf olds T) #[]).toList := by
  induction l with
  | nil =>
    intro tab _ T h
    rcases h with h | h
    · simp at h
    · exact h
  | cons T0 t ih =>
    intro tab hsz T h
    rw [List.foldl_cons]
    apply ih _ (by rw [Array.size_modify, hsz]) T
    have hk : keyOf olds T < (tab.modify (keyOf olds T0) (·.push T0)).size := by
      rw [Array.size_modify, hsz]; exact keyOf_lt olds T
    have hk' : keyOf olds T < tab.size := by rw [hsz]; exact keyOf_lt olds T
    rw [getD_of_lt _ _ hk, Array.getElem_modify hk]
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · right
        rw [if_pos rfl]
        simp
      · exact Or.inl h
    · right
      rw [getD_of_lt _ _ hk'] at h
      split
      · simp only [Array.toList_push, List.mem_append]
        exact Or.inl h
      · exact h

theorem mkBuckets_mem (olds : Array (ℕ × ℕ × ℕ)) (R : Array Fast.Pat) {T : Fast.Pat}
    (hT : T ∈ R.toList) :
    T ∈ ((Fast.mkBuckets olds R).getD (keyOf olds T) #[]).toList := by
  unfold Fast.mkBuckets
  rw [← Array.foldl_toList]
  exact buckets_fold olds R.toList _ Array.size_replicate T (Or.inl hT)

/-! ### The specification -/

theorem levelSpec_mkLevel {n : ℕ} (R : Array Fast.Pat) (hcov : covOk n = true) :
    LevelSpec (Fast.mkLevel n R) R := by
  unfold covOk at hcov
  rw [Bool.and_eq_true] at hcov
  obtain ⟨hc1, hc2⟩ := hcov
  have hcov1 : ∀ pos < (Fast.combos n).length, ∃ j, ∃ hj : j < (pmsOf n).size,
      pos ∈ (pmsOf n)[j] := by
    intro pos hpos
    have h := List.all_eq_true.1 hc1 pos (List.mem_range.2 hpos)
    obtain ⟨j, hj, hjc⟩ := List.any_eq_true.1 h
    have hj' : j < n := List.mem_range.1 hj
    have hsz : j < (pmsOf n).size := by unfold pmsOf; rw [Array.size_ofFn]; exact hj'
    refine ⟨j, hsz, ?_⟩
    rw [← getD_of_lt _ #[] hsz, pmsOf_getD hj']
    have : pos ∈ (Fast.pmOf n (n - 1 - j)).toList := by simpa using hjc
    exact Array.mem_def.2 this
  have hcov2 : ∀ j < n, ∀ k < (Fast.pmOf n (n - 1 - j)).size,
      (Fast.pmOf n (n - 1 - j)).getD k 0 < (Fast.combos n).length := by
    intro j hj k hk
    have h := List.all_eq_true.1 (List.all_eq_true.1 hc2 j (List.mem_range.2 hj))
      ((Fast.pmOf n (n - 1 - j)).getD k 0)
      (by rw [getD_of_lt _ _ hk]; exact Array.getElem_mem_toList hk)
    exact of_decide_eq_true h
  have hpsz : (pmsOf n).size = n := by unfold pmsOf; rw [Array.size_ofFn]
  have hssz : (Fast.mkLevel n R).stages.size = n := by rw [mkLevel_stages, Array.size_ofFn]
  -- the source of a position
  have hsrc : ∀ pos < (Fast.combos n).length,
      ((srcOf n).getD pos (0, 0)).1 < n ∧
      ((srcOf n).getD pos (0, 0)).2
        < (Fast.pmOf n (n - 1 - ((srcOf n).getD pos (0, 0)).1)).size ∧
      (Fast.pmOf n (n - 1 - ((srcOf n).getD pos (0, 0)).1)).getD ((srcOf n).getD pos (0, 0)).2 0
        = pos := by
    intro pos hpos
    have e : (srcOf n).getD pos (0, 0) = Fast.findSrc (pmsOf n) pos := getD_ofFn _ _ hpos
    obtain ⟨h1, h2, h3⟩ := findSrc_spec (pmsOf n) pos (hcov1 pos hpos)
    rw [hpsz] at h1
    rw [pmsOf_getD h1] at h2 h3
    rw [e]
    exact ⟨h1, h2, h3⟩
  refine ⟨hssz, rfl, ?_, ?_, ?_, ?_⟩
  · intro pos hpos
    obtain ⟨h1, h2, h3⟩ := hsrc pos hpos
    rw [mkLevel_src, hssz, stage_getD h1]
    exact ⟨h1, h2, h3⟩
  · intro s hs o ho
    rw [hssz] at hs
    rw [stage_getD hs] at ho ⊢
    simp only at ho ⊢
    unfold oldsOf at ho
    rw [Array.toList_filterMap, List.mem_filterMap] at ho
    obtain ⟨k, hk, hko⟩ := ho
    rw [pmsOf_getD hs] at hk hko
    have hk' : k < (Fast.pmOf n (n - 1 - s)).size := by simpa using hk
    have hjk := hsrc _ (hcov2 s hs k hk')
    dsimp only at hko
    generalize (srcOf n).getD ((Fast.pmOf n (n - 1 - s)).getD k 0) (0, 0) = jk at hko hjk
    by_cases hlt : jk.1 < s
    · rw [if_pos hlt] at hko
      obtain rfl := Option.some.inj hko
      obtain ⟨h1, h2, h3⟩ := hjk
      rw [stage_getD h1]
      exact ⟨hlt, hk', h2, h3⟩
    · rw [if_neg hlt] at hko
      exact absurd hko (by simp)
  · intro j hj
    have hj' : j < n := hj
    rw [stage_getD hj']
    rfl
  · intro s hs T hT
    rw [hssz] at hs
    rw [stage_getD hs]
    exact mkBuckets_mem (oldsOf n s) R hT

end BeatAvg
