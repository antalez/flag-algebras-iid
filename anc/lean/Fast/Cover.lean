import Fast.Pat

/-!
# Enumeration of patterns by joins (computable part)

Level `n`: all patterns `P` on `n` points such that, for each deleted point `d`, the restriction of
`P` to the other `n - 1` points lies in a given list `R`. Stage `j` deletes the point `n - 1 - j`.
-/

namespace Fast

abbrev Pat := Array Nat

def skipQ (d : Nat) (q : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (skip d q.1, skip d q.2.1, skip d q.2.2.1, skip d q.2.2.2)

/-- Positions in the `n`-point pattern of the quadruples of the `(n-1)`-point pattern, after
inserting the point `d`. -/
def pmOf (n d : Nat) : Array Nat := ((combos (n - 1)).map fun q => comboIdx n (skipQ d q)).toArray

/-- Number of buckets. -/
def nBuckets : Nat := 1048576

structure Stage where
  pm : Array Nat
  /-- `(k, j, k')`: entry `k` of this stage's pattern must equal entry `k'` of stage `j < s`. -/
  olds : Array (Nat × Nat × Nat)
  buckets : Array (Array Pat)

structure Level where
  n : Nat
  m : Nat
  stages : Array Stage
  /-- For each position of the `n`-point pattern: a stage and an entry that determine it. -/
  src : Array (Nat × Nat)

def keyT (st : Stage) (T : Pat) : Nat :=
  st.olds.toList.foldl (fun acc o => (acc * 3 + T.getD o.1 0) % nBuckets) 0

def keyS (st : Stage) (chosen : List Pat) : Nat :=
  st.olds.toList.foldl (fun acc o => (acc * 3 + (chosen.getD o.2.1 #[]).getD o.2.2 0) % nBuckets) 0

def matchesOld (st : Stage) (chosen : List Pat) (T : Pat) : Bool :=
  st.olds.toList.all fun o => T.getD o.1 0 == (chosen.getD o.2.1 #[]).getD o.2.2 0

def cands (st : Stage) (chosen : List Pat) : List Pat :=
  ((st.buckets.getD (keyS st chosen) #[]).toList).filter (matchesOld st chosen)

def assemble (L : Level) (chosen : List Pat) : Pat :=
  Array.ofFn (n := L.m) fun pos =>
    (chosen.getD (L.src.getD pos.val (0, 0)).1 #[]).getD (L.src.getD pos.val (0, 0)).2 0

/-- All leaves `P` of the join tree below `chosen` with `keep P`. -/
def go (L : Level) (keep : Pat → Bool) : Nat → List Pat → List Pat
  | 0, chosen => let P := assemble L chosen; if keep P then [P] else []
  | rem + 1, chosen =>
    (cands (L.stages.getD chosen.length ⟨#[], #[], #[]⟩) chosen).flatMap fun T =>
      go L keep rem (chosen ++ [T])

/-! ### Building a level -/

def findSrc (pms : Array (Array Nat)) (pos : Nat) : Nat × Nat :=
  let j := (pms.findIdx? fun pm => pm.contains pos).getD 0
  (j, ((pms.getD j #[]).idxOf? pos).getD 0)

def mkBuckets (olds : Array (Nat × Nat × Nat)) (R : Array Pat) : Array (Array Pat) :=
  R.foldl (fun tab T =>
    tab.modify (olds.toList.foldl (fun acc o => (acc * 3 + T.getD o.1 0) % nBuckets) 0) (·.push T))
    (Array.replicate nBuckets #[])

def mkLevel (n : Nat) (R : Array Pat) : Level :=
  let m := (combos n).length
  let pms : Array (Array Nat) := Array.ofFn (n := n) fun j => pmOf n (n - 1 - j.val)
  let src : Array (Nat × Nat) := Array.ofFn (n := m) fun pos => findSrc pms pos.val
  let stages : Array Stage := Array.ofFn (n := n) fun s =>
    let pm := pms.getD s.val #[]
    let olds : Array (Nat × Nat × Nat) := (List.range pm.size).toArray.filterMap fun k =>
      let jk := src.getD (pm.getD k 0) (0, 0)
      if jk.1 < s.val then some (k, jk.1, jk.2) else none
    ⟨pm, olds, mkBuckets olds R⟩
  ⟨n, m, stages, src⟩

/-! ### Checkable properties of a level -/

def srcOk (L : Level) : Bool :=
  (List.range L.m).all fun pos =>
    let jk := L.src.getD pos (0, 0)
    decide (jk.1 < L.stages.size) &&
      decide (jk.2 < (L.stages.getD jk.1 ⟨#[], #[], #[]⟩).pm.size) &&
      (L.stages.getD jk.1 ⟨#[], #[], #[]⟩).pm.getD jk.2 0 == pos

def oldsOk (L : Level) : Bool :=
  (List.range L.stages.size).all fun s =>
    let st := L.stages.getD s ⟨#[], #[], #[]⟩
    st.olds.toList.all fun o =>
      decide (o.2.1 < s) && decide (o.1 < st.pm.size) &&
        decide (o.2.2 < (L.stages.getD o.2.1 ⟨#[], #[], #[]⟩).pm.size) &&
        (L.stages.getD o.2.1 ⟨#[], #[], #[]⟩).pm.getD o.2.2 0 == st.pm.getD o.1 0

/-- Stage `j` uses the position map of the deleted point `n - 1 - j`. -/
def pmOk (L : Level) : Bool :=
  (List.range L.n).all fun j => (L.stages.getD j ⟨#[], #[], #[]⟩).pm == pmOf L.n (L.n - 1 - j)

/-- Every pattern of `R` is found in its bucket, at every stage. For a stage without constraints
the single bucket is compared with `R` as a whole. -/
def bucketsOk (L : Level) (R : Array Pat) : Bool :=
  (List.range L.stages.size).all fun s =>
    let st := L.stages.getD s ⟨#[], #[], #[]⟩
    if st.olds.isEmpty then st.buckets.getD 0 #[] == R
    else R.toList.all fun T => (st.buckets.getD (keyT st T) #[]).toList.contains T

def levelOk (L : Level) (R : Array Pat) : Bool :=
  L.stages.size == L.n && L.m == (combos L.n).length && L.src.size == L.m &&
    srcOk L && oldsOk L && pmOk L && bucketsOk L R

end Fast

namespace Fast

/-- No leaf below any first-stage choice is kept; one task per first-stage choice. -/
def goPar (L : Level) (keep : Pat → Bool) : Bool :=
  ((cands (L.stages.getD 0 ⟨#[], #[], #[]⟩) []).map fun T =>
    Task.spawn fun _ => (go L keep (L.n - 1) [T]).isEmpty).all Task.get

/-- Number of leaves (for testing). -/
def goCountPar (L : Level) : Nat :=
  ((cands (L.stages.getD 0 ⟨#[], #[], #[]⟩) []).map fun T =>
    Task.spawn fun _ => (go L (fun _ => true) (L.n - 1) [T]).length).foldl (fun a t => a + t.get) 0

end Fast
