/-!
# Canonical arrangements (computable part)

An arrangement is a list of eight elements of `Fin 8`. `canonL blocks` sorts the values inside each
block of positions. The representatives are the orderings of `0..7` fixed by `canonL`.
-/

namespace Fast

/-- The function `Fin 8 → Fin 8` of a list. -/
@[inline] def fnOf (l : List (Fin 8)) : Fin 8 → Fin 8 := fun i => l.getD i.val 0

/-- Insert `x` at every position of `l`. -/
def insertAll {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- All orderings of a list. -/
def allOrders {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (allOrders xs).flatMap (insertAll x)

/-- Sort the values at the positions `ps` (given in increasing order). -/
def sortBlock (a : Array (Fin 8)) (ps : List Nat) : Array (Fin 8) :=
  let vals := (ps.map fun p => a[p]!).mergeSort (fun x y => decide (x ≤ y))
  (ps.zip vals).foldl (fun acc pv => acc.set! pv.1 pv.2) a

def canonL (blocks : List (List Nat)) (l : List (Fin 8)) : List (Fin 8) :=
  (blocks.foldl sortBlock l.toArray).toList

/-- The values at the positions `ps` (taken in order) increase. -/
def chainLt (l : List (Fin 8)) : List Nat → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => decide (l.getD p 0 < l.getD q 0) && chainLt l (q :: rest)

/-- The values increase inside each block of positions. -/
def blockSorted (blocks : List (List Nat)) (l : List (Fin 8)) : Bool := blocks.all (chainLt l)

/-- The orderings of `0..7` that increase inside each block (structural recursion only, so that
the kernel can evaluate it). -/
def repsOf (blocks : List (List Nat)) : List (List (Fin 8)) :=
  (allOrders (List.finRange 8)).filter (blockSorted blocks)

def blocksObj : List (List Nat) := [[0, 1, 2], [4, 5, 6, 7]]
def blocksSq : List (List Nat) := [[0, 1], [2, 3, 4], [5, 6, 7]]
def blocksDeg : List (List Nat) := [[1, 2, 3, 4], [5, 6]]
def blocksThr : List (List Nat) := [[0, 1, 2, 3], [4, 5, 6]]

def repsObj : List (List (Fin 8)) := repsOf blocksObj
def repsSq : List (List (Fin 8)) := repsOf blocksSq
def repsDeg : List (List (Fin 8)) := repsOf blocksDeg
def repsThr : List (List (Fin 8)) := repsOf blocksThr

end Fast
