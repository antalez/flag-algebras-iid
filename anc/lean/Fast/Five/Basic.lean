import Fast.K

/-! Computable definitions for the five-point colored certificate.
These import no eight-point data and no Mathlib. -/
namespace Fast.Five

abbrev Pattern := Nat

/-- Increasing subsets, in lexicographic order. -/
def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map (i, ·)

def quads (n : Nat) : List (List Nat) := choose 4 (List.range n)

def edge (p : Pattern) (i j : Nat) : Bool :=
  p.testBit ((pairs 5).idxOf (i,j))

def win (p : Pattern) (v : List Nat) (k : Nat) : Bool :=
  p.testBit (10 + 2 * (quads 5).idxOf v + (k - 2))

/-- Number of winning targets on a four-point subset. -/
def wins (p : Pattern) (v : List Nat) : Nat :=
  (if win p v 2 then 1 else 0) + (if win p v 3 then 1 else 0)

/-- Code of an induced sorted subpattern, with local pair bits first. -/
def code (p : Pattern) (v : List Nat) : Nat := Id.run do
  let mut out := 0
  let mut pos := 0
  for (i,j) in pairs v.length do
    if edge p (v.getD i 0) (v.getD j 0) then out := out + 2^pos
    pos := pos + 1
  for q in quads v.length do
    let actual := q.map (fun i => v.getD i 0)
    for k in [2,3] do
      if win p actual k then out := out + 2^pos
      pos := pos + 1
  return out

/-- Merge two disjoint increasing index sets. -/
def unionSorted (a b : List Nat) : List Nat := (List.range 5).filter fun i => i ∈ a ∨ i ∈ b

def flagCode (p : Pattern) (roots extras : List Nat) : Nat :=
  let v := unionSorted roots extras
  let marks := choose roots.length (List.range v.length)
  code p v * marks.length + marks.idxOf (roots.map (v.idxOf ·))

/-- Original coordinates of the 20 linear forms, negative when their bit is true. -/
def form (i : Nat) : List Int :=
  if i < 10 then
    let ij := (pairs 5).getD i (0,0)
    (List.range 5).map fun j => (if j = ij.2 then 1 else 0) - (if j = ij.1 then 2 else 0)
  else
    let v := (quads 5).getD ((i-10)/2) []
    let target := v.getD (2+(i-10)%2) 0
    (List.range 5).map fun j => (if j ∈ v then 1 else 0) - (if j = target then 3 else 0)

/-- Coefficients in positive successive gaps. -/
def gapForm (i j : Nat) : Int := ((form i).drop j).sum

/-- A full binary partition, with retained-pattern or Gordan leaves. -/
inductive Cover where
  | branch : Cover → Cover → Cover
  | retained : Nat → Cover
  | excluded : List (Nat × Nat) → Cover
  deriving Repr

/-- Excluded prefixes have a positive combination of strict negative forms
whose gap coefficients are all nonnegative. -/
def exclusionOk (depth bits : Nat) (w : List (Nat × Nat)) : Bool :=
  !w.isEmpty && w.all (fun e => decide (e.1 < depth ∧ 0 < e.2)) &&
  (List.range 5).all (fun j => decide (0 ≤ (w.map fun e =>
    (e.2 : Int) * (if bits.testBit e.1 then 1 else -1) * gapForm e.1 j).sum))

def coverOk (patterns : Array Nat) : Cover → Nat → Nat → Bool
  | .branch a b, depth, bits => decide (depth < 20) &&
      coverOk patterns a (depth+1) (bits+2^depth) && coverOk patterns b (depth+1) bits
  | .retained i, depth, bits => decide (depth = 20 ∧ i < patterns.size) && patterns[i]! == bits
  | .excluded w, depth, bits => decide (depth ≤ 20) && exclusionOk depth bits w

end Fast.Five
