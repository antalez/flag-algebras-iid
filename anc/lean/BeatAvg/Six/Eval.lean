import BeatAvg.Six.Data
import Fast.Psd
import Fast.Gen

/-!
# The six-point flag certificate: evaluation (definitions)

Everything here is structurally recursive on lists, so that the kernel can evaluate it
(`decide +kernel`). No compiled code is used.

Families (`t` roots, `m` further points in each of the two extensions), on the positions `0..5`:

* `A`: `t = 2, m = 2`, roots `0 1`, extensions `2 3` and `4 5`;
* `B`: `t = 3, m = 1`, roots `0 1 2`, extensions `3` and `4` (position `5` is not used);
* `C`: `t = 4, m = 1`, roots `0 1 2 3`, extensions `4` and `5`.

The objective uses the positions `0 1 2` (summands) and `3` (target).
-/

namespace BeatAvg.Six

/-- Position of the quadruple `a < b < c < d < 6` in `Fast.combos 6`. -/
def idxTab : List (List (List (List Nat))) :=
  [[[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 4], [0, 0, 0, 0, 0, 5], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 6, 7], [0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]],
   [[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 10, 11], [0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 13], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]],
   [[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 14], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]],
   [[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]],
   [[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]],
   [[[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]]]

def idx6 (a b c d : Nat) : Nat := (((idxTab.getD a []).getD b []).getD c []).getD d 0

/-- The configuration of a sorted sample of six points with pattern `P`. -/
def cfg6 (P : Array Nat) : Fast.Cfg 6 := Fast.cfgOfPatG 6 idx6 P

/-! ### Arrangements -/

/-- The function `Fin 6 → Fin 6` of a list. -/
def fnOf6 (l : List (Fin 6)) : Fin 6 → Fin 6 := fun i => l.getD i.val 0

def chainLt6 (l : List (Fin 6)) : List Nat → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => decide (l.getD p 0 < l.getD q 0) && chainLt6 l (q :: rest)

/-- The orderings of `0..5` that increase inside each block of positions. -/
def repsOf6 (blocks : List (List Nat)) : List (List (Fin 6)) :=
  (Fast.allOrders (List.finRange 6)).filter fun l => blocks.all (chainLt6 l)

def repsA : List (List (Fin 6)) := repsOf6 [[0, 1], [2, 3], [4, 5]]
def repsB : List (List (Fin 6)) := repsOf6 [[0, 1, 2]]
def repsC : List (List (Fin 6)) := repsOf6 [[0, 1, 2, 3]]
def repsO : List (List (Fin 6)) := repsOf6 [[0, 1, 2], [4, 5]]

/-- Index maps of a family. -/
def eR6 (t : Nat) (i : Fin t) : Fin 6 := Fin.ofNat 6 i.val
def eT6 (t m : Nat) (j : Fin m) : Fin 6 := Fin.ofNat 6 (t + j.val)
def eT6' (t m : Nat) (j : Fin m) : Fin 6 := Fin.ofNat 6 (t + m + j.val)

/-- Positions of the objective term. -/
def e46 (i : Fin 4) : Fin 6 := Fin.ofNat 6 i.val

/-! ### Flags -/

/-- The candidate inequalities `(i, j, k; l)` of `f` sorted points, in the order of the
certificate: `x_i + x_j + x_k < 2 x_l` with `l` one of the two largest of the four. -/
def cand4 : List (Nat × Nat × Nat × Nat) := [(0, 1, 2, 3), (0, 1, 3, 2)]
def cand5 : List (Nat × Nat × Nat × Nat) := 
  [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 2), (0, 1, 3, 4), (0, 1, 4, 2), (0, 1, 4, 3), (0, 2, 3, 4), (0, 2, 4, 3), (1, 2, 3, 4), (1, 2, 4, 3)]

/-- Key of the flag of `t` sorted roots (positions `0..t-1`) followed by `m` sorted further
points: `bits * 64 + mask`. Bit `j` of `bits` says that candidate `j` succeeds on the points in
increasing order; `mask` is the set of ranks of the roots. -/
def flagKey (cand : List (Nat × Nat × Nat × Nat)) (t m : Nat) (c : Fast.Cfg (t + m)) : Nat :=
  let pts := List.finRange (t + m)
  -- `q` comes before `p`
  let before (q p : Fin (t + m)) : Bool :=
    if decide (q.val < t) == decide (p.val < t) then decide (q.val < p.val) else c.lt q p
  let ranks : List Nat := pts.map fun p => pts.countP fun q => before q p
  -- the points by increasing rank
  let arr : List (Fin (t + m)) := (List.range (t + m)).filterMap fun r =>
    ((pts.zip ranks).find? fun pr => pr.2 == r).map (·.1)
  let ok (q : Nat × Nat × Nat × Nat) : Bool :=
    match arr[q.1]?, arr[q.2.1]?, arr[q.2.2.1]?, arr[q.2.2.2]? with
    | some a, some b, some e, some d => c.sb a b e d
    | _, _, _, _ => false
  let bits := cand.foldr (fun q acc => acc * 2 + (if ok q then 1 else 0)) 0
  let mask := (ranks.take t).foldl (fun acc r => acc + 2 ^ r) 0
  bits * 64 + mask

/-- A family: keys of its flags, block of each flag, integer row of each flag. -/
structure FamData where
  keys : List Nat
  blk : List Nat
  rows : List (List Nat)

def famA : FamData := ⟨D.keysA, D.blkA, D.rowsA⟩
def famB : FamData := ⟨D.keysB, D.blkB, D.rowsB⟩
def famC : FamData := ⟨D.keysC, D.blkC, D.rowsC⟩

/-- Index of the flag in the family. -/
def flagIdx (d : FamData) (cand : List (Nat × Nat × Nat × Nat)) (t m : Nat)
    (c : Fast.Cfg (t + m)) : Nat :=
  d.keys.idxOf (flagKey cand t m c)

/-- Integer row of flag `i`. -/
def rowOf (d : FamData) (i : Nat) : List Int :=
  (d.rows.getD i []).map fun x : Nat => (x : Int) - D.off

/-- Entry of `den · Q`: the Gram matrix of the rows inside a block, zero across blocks. -/
def QI (d : FamData) (i j : Nat) : Int :=
  if d.blk.getD i 0 = d.blk.getD j 0 then Fast.dotL (rowOf d i) (rowOf d j) else 0

/-- Sum over the arrangements `reps` of the square term of a family. -/
def famSum (d : FamData) (cand : List (Nat × Nat × Nat × Nat)) (t m : Nat)
    (reps : List (List (Fin 6))) (c : Fast.Cfg 6) : Int :=
  (reps.map fun l =>
    QI d (flagIdx d cand t m (c.comap (fnOf6 l ∘ Fast.appendF (eR6 t) (eT6 t m))) % d.keys.length)
      (flagIdx d cand t m (c.comap (fnOf6 l ∘ Fast.appendF (eR6 t) (eT6' t m)))
        % d.keys.length)).sum

def objCount (c : Fast.Cfg 6) : Nat :=
  repsO.countP fun l => c.sb (fnOf6 l (e46 0)) (fnOf6 l (e46 1)) (fnOf6 l (e46 2)) (fnOf6 l (e46 3))

/-- `6! · den · Λ` for the configuration `c`. -/
def total6 (c : Fast.Cfg 6) : Int :=
  12 * D.den * (objCount c : Int) + 8 * famSum famA cand4 2 2 repsA c
    + 6 * famSum famB cand4 3 1 repsB c + 24 * famSum famC cand5 4 1 repsC c

/-- The pattern `v` (trits of the quadruples of `Fast.combos 6`) satisfies the certificate
inequality with the bound `lamP / lamQ`. -/
def eval6 (v : List Nat) : Bool :=
  decide (total6 (cfg6 v.toArray) * D.lamQ ≤ 720 * D.den * D.lamP)

end BeatAvg.Six
