import Fast.Gen
import Fast.Canon7
import Fast.Data
import Std.Data.HashMap

/-!
# The order-7 flag certificate (computable part)
-/

namespace Fast

structure Cert7 where
  /-- per family: key ↦ flag index -/
  keys : Array (Std.HashMap Nat Nat)
  /-- per family: block of each flag -/
  blk : Array (Array Nat)
  /-- per family: integer row of each flag (`Q = L L^T / 4^scale` inside a block) -/
  rows : Array (Array (Array Int))
  /-- per family: (row length, number of flags, number of blocks) -/
  dims : Array (Nat × Nat × Nat)
  num : Int
  den : Int
  scale : Nat

def parseCert7 (s : String) : Cert7 := Id.run do
  let mut keys : Array (Std.HashMap Nat Nat) := Array.replicate 5 {}
  let mut blk : Array (Array Nat) := Array.replicate 5 #[]
  let mut rows : Array (Array (Array Int)) := Array.replicate 5 #[]
  let mut dims : Array (Nat × Nat × Nat) := Array.replicate 5 (0, 0, 0)
  let mut num : Int := 0
  let mut den : Int := 1
  let mut scale : Nat := 0
  for line in s.splitOn "\n" do
    match line.splitOn " " with
    | [] => pure ()
    | kw :: rest =>
      let v : List Int := rest.filterMap String.toInt?
      match kw, v with
      | "BOUND", [a, b] => num := a; den := b
      | "SCALE", [a] => scale := a.toNat
      | "LEN", [k, l, n, nb] => dims := dims.set! k.toNat (l.toNat, n.toNat, nb.toNat)
      | "F", k :: _i :: key :: b :: row =>
        let i := (blk.getD k.toNat #[]).size
        keys := keys.modify k.toNat (fun m => m.insert key.toNat i)
        blk := blk.modify k.toNat (·.push b.toNat)
        rows := rows.modify k.toNat (·.push row.toArray)
      | _, _ => pure ()
  return ⟨keys, blk, rows, dims, num, den, scale⟩

/-- Key of the flag of `t` sorted roots (positions `0..t-1`) and `m` sorted further points:
`code * 64 + mask`, with `code` the pattern of the `t + m` points in increasing order and `mask`
the set of ranks of the roots. -/
def flagKey (t m : Nat) (c : Cfg (t + m)) : Nat :=
  let pts := List.finRange (t + m)
  -- `q` comes before `p`
  let before (q p : Fin (t + m)) : Bool :=
    if decide (q.val < t) == decide (p.val < t) then decide (q.val < p.val) else c.lt q p
  let rank (p : Fin (t + m)) : Nat := pts.countP fun q => before q p
  let arr : Array (Fin (t + m)) := (pts.mergeSort fun p q => decide (rank p ≤ rank q)).toArray
  let trit (q : Nat × Nat × Nat × Nat) : Nat :=
    match arr[q.1]?, arr[q.2.1]?, arr[q.2.2.1]?, arr[q.2.2.2]? with
    | some a, some b, some e, some d =>
      (if c.sb a b e d then 1 else 0) + (if c.sb a b d e then 1 else 0)
    | _, _, _, _ => 0
  let code := (combos (t + m)).foldr (fun q acc => acc * 3 + trit q) 0
  let mask := (pts.filter fun p => decide (p.val < t)).foldl (fun acc p => acc + 2 ^ rank p) 0
  code * 64 + mask

/-- Flag index in family `k`. -/
def flag7 (c7 : Cert7) (k t m : Nat) (c : Cfg (t + m)) : Nat :=
  ((c7.keys.getD k {})[flagKey t m c]?).getD 0

def dotI (len : Nat) (a b : Array Int) : Int :=
  ((List.range len).map fun i => a.getD i 0 * b.getD i 0).sum

/-- Integer entry of `4^scale · Q` in family `k`. -/
def QI (c7 : Cert7) (k : Nat) (i j : Nat) : Int :=
  if (c7.blk.getD k #[]).getD i 0 = (c7.blk.getD k #[]).getD j 0 then
    dotI (c7.dims.getD k (0, 0, 0)).1 ((c7.rows.getD k #[]).getD i #[]) ((c7.rows.getD k #[]).getD j #[])
  else 0

/-- Number of flags of family `k`. -/
def nFlags (c7 : Cert7) (k : Nat) : Nat := (c7.dims.getD k (0, 0, 0)).2.1

/-- Sum over the arrangements `reps` of the square term of family `k`. -/
def famSum (c7 : Cert7) (k t m : Nat) (reps : List (List (Fin 7))) (c : Cfg 7) : Int :=
  (reps.map fun l =>
    QI c7 k (flag7 c7 k t m (c.comap (fnOf7 l ∘ appendF (eR7 t) (eT7 t m))) % nFlags c7 k)
      (flag7 c7 k t m (c.comap (fnOf7 l ∘ appendF (eR7 t) (eT7' t m))) % nFlags c7 k)).sum

def objCount7 (c : Cfg 7) : Nat :=
  repsObj7.countP fun l => c.sb (fnOf7 l (e47 0)) (fnOf7 l (e47 1)) (fnOf7 l (e47 2)) (fnOf7 l (e47 3))

/-- `7! · 4^scale · Λ` for the configuration `c`. -/
def total7 (c7 : Cert7) (c : Cfg 7) : Int :=
  36 * 4 ^ c7.scale * (objCount7 c : Int) + 36 * famSum c7 0 1 3 reps14 c + 8 * famSum c7 1 2 2 reps24 c
    + 24 * famSum c7 2 3 2 reps35 c + 24 * famSum c7 3 4 1 reps45 c + 120 * famSum c7 4 5 1 reps56 c

/-- The pattern `P` satisfies the certificate inequality with the bound `801509 / 2000000`. -/
def eval7 (c7 : Cert7) (P : Pat) : Bool :=
  decide (2000000 * total7 c7 (cfgOfPatG 7 idx7 P) ≤ 5040 * 4 ^ c7.scale * 801509)

def cert7Str : String := include_str "../data/cert7.txt"

def cert7 : Cert7 := parseCert7 cert7Str

/-- The whole order-7 check. -/
def check7 (_ : Unit) : Bool :=
  (R7.toList.map fun P => Task.spawn fun _ => eval7 cert7 P).all Task.get

end Fast

namespace Fast

/-- Block of flag `i` in family `k`. -/
def blk7 (c7 : Cert7) (k i : Nat) : Nat := (c7.blk.getD k #[]).getD i 0

/-- Static checks of the order-7 certificate. -/
def static7 (c7 : Cert7) : Bool :=
  (List.range 5).all fun k =>
      decide (0 < nFlags c7 k) &&
        (List.range (nFlags c7 k)).all fun i => decide (blk7 c7 k i < (c7.dims.getD k (0, 0, 0)).2.2)

end Fast
