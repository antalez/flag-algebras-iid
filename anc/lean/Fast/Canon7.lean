import Fast.Canon

/-!
# Canonical arrangements of seven points (computable part)
-/

namespace Fast

/-- The function `Fin 7 → Fin 7` of a list. -/
@[inline] def fnOf7 (l : List (Fin 7)) : Fin 7 → Fin 7 := fun i => l.getD i.val 0

def sortBlock7 (a : Array (Fin 7)) (ps : List Nat) : Array (Fin 7) :=
  let vals := (ps.map fun p => a[p]!).mergeSort (fun x y => decide (x ≤ y))
  (ps.zip vals).foldl (fun acc pv => acc.set! pv.1 pv.2) a

def canonL7 (blocks : List (List Nat)) (l : List (Fin 7)) : List (Fin 7) :=
  (blocks.foldl sortBlock7 l.toArray).toList

def chainLt7 (l : List (Fin 7)) : List Nat → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => decide (l.getD p 0 < l.getD q 0) && chainLt7 l (q :: rest)

def blockSorted7 (blocks : List (List Nat)) (l : List (Fin 7)) : Bool := blocks.all (chainLt7 l)

/-- The orderings of `0..6` that increase inside each block. -/
def repsOf7 (blocks : List (List Nat)) : List (List (Fin 7)) :=
  (allOrders (List.finRange 7)).filter (blockSorted7 blocks)

/-- Blocks of a family with `t` roots and `m` further points: positions `0..t-1`, `t..t+m-1`,
`t+m..t+2m-1`. -/
def blocksFam (t m : Nat) : List (List Nat) :=
  [List.range t, (List.range m).map (· + t), (List.range m).map (· + t + m)]

def blocksObj7 : List (List Nat) := [[0, 1, 2], [4, 5, 6]]

def repsObj7 : List (List (Fin 7)) := repsOf7 blocksObj7
def reps14 : List (List (Fin 7)) := repsOf7 (blocksFam 1 3)
def reps24 : List (List (Fin 7)) := repsOf7 (blocksFam 2 2)
def reps35 : List (List (Fin 7)) := repsOf7 (blocksFam 3 2)
def reps45 : List (List (Fin 7)) := repsOf7 (blocksFam 4 1)
def reps56 : List (List (Fin 7)) := repsOf7 (blocksFam 5 1)

/-- Index maps of a family on seven points. -/
def eR7 (t : Nat) (i : Fin t) : Fin 7 := Fin.ofNat 7 i.val
def eT7 (t m : Nat) (j : Fin m) : Fin 7 := Fin.ofNat 7 (t + j.val)
def eT7' (t m : Nat) (j : Fin m) : Fin 7 := Fin.ofNat 7 (t + m + j.val)

/-- Positions of the objective term. -/
def e47 (i : Fin 4) : Fin 7 := Fin.ofNat 7 i.val

end Fast
