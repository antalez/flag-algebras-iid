import Fast.Five.Check
import Fast.Five.Config
import Fast.Gen
import Fast.Canon

/-! Four-point ratio patterns. Matrix storage and arithmetic are shared with
the five-point proof; the comparisons and sample functional are new. -/
namespace Fast.Four

abbrev Pattern := Nat
abbrev Block := Fast.Five.Block
abbrev choose := Fast.Five.choose
abbrev pairs := Fast.Five.pairs
abbrev ksum := Fast.Five.ksum
abbrev lower := Fast.Five.lower
abbrev keq := Fast.Five.keq
abbrev entryAt := Fast.Five.entryAt
abbrev expandedEntry := Fast.Five.expandedEntry
abbrev expandedRow := Fast.Five.expandedRow
abbrev psdRow := Fast.Five.psdRow

def cutNum (q : Fin 3) : Int := if q.val = 0 then 7 else if q.val = 1 then 3 else 2
def cutDen (q : Fin 3) : Int := if q.val = 0 then 6 else if q.val = 1 then 2 else 1

def edge (p : Pattern) (i j q : Nat) : Bool :=
  p.testBit (3 * (pairs 4).idxOf (i,j) + q)

def wins (p : Pattern) : Nat :=
  (if p.testBit 18 then 1 else 0) + (if p.testBit 19 then 1 else 0)

/-- Integer multiples of the twenty linear comparisons, negative for a true bit. -/
def form (i : Nat) : List Int :=
  if i < 18 then
    let ij := (pairs 4).getD (i/3) (0,0)
    let q := Fin.ofNat 3 i
    (List.range 4).map fun j =>
      (if j = ij.2 then cutDen q else 0) - (if j = ij.1 then cutNum q else 0)
  else
    let target := if i = 18 then 3 else 2
    (List.range 4).map fun j => if j = target then -2 else 1

def gapForm (i j : Nat) : Int := ((form i).drop j).sum

abbrev Cover := Fast.Five.Cover

def exclusionOk (depth bits : Nat) (w : List (Nat × Nat)) : Bool :=
  !w.isEmpty && w.all (fun e => decide (e.1 < depth ∧ 0 < e.2)) &&
  (List.range 4).all (fun j => decide (0 ≤ (w.map fun e =>
    (e.2 : Int) * (if bits.testBit e.1 then 1 else -1) * gapForm e.1 j).sum))

def coverOk (patterns : Array Nat) : Cover → Nat → Nat → Bool
  | .branch a b, depth, bits => decide (depth < 20) &&
      coverOk patterns a (depth+1) (bits+2^depth) && coverOk patterns b (depth+1) bits
  | .retained i, depth, bits => decide (depth = 20 ∧ i < patterns.size) && patterns[i]! == bits
  | .excluded w, depth, bits => decide (depth ≤ 20) && exclusionOk depth bits w

/-- Matrix-only metadata view for reusing the existing matrix shape theorem.
Its basis, matrix, Gram witness, flags, and expanded entries are unchanged. -/
def matrixView (b : Block) : Block := { b with roots := 1, flagSize := 3 }

def blockShape (b : Block) : Bool :=
  decide (b.roots = 2 ∧ b.flagSize = 3) && Fast.Five.blockShape (matrixView b)

structure Config (n : Nat) where
  additive : Fast.Cfg n
  close : Fin 3 → Fin n → Fin n → Bool

def bitNat (b : Bool) : Nat := if b then 1 else 0

def color {n : Nat} (c : Config n) (a b : Fin n) : Nat :=
  bitNat (c.close 0 a b) + 2 * bitNat (c.close 1 a b) + 4 * bitNat (c.close 2 a b)

def code3 (c : Config 3) (a b d : Fin 3) : Nat :=
  color c a b + 8 * color c a d + 64 * color c b d

/-- Two sorted roots at positions 0,1, followed by one extension at position 2. -/
def pairFlag (b : Block) (c : Config 3) : Nat :=
  if color c 0 1 != b.ty then b.flags.size else
    let p := bitNat (c.additive.lt 0 2) + bitNat (c.additive.lt 1 2)
    let inv : Nat → Fin 3 := fun k =>
      if k = p then 2 else Fin.ofNat 3 (k - bitNat (decide (p < k)))
    b.flags.toList.idxOf (3 * code3 c (inv 0) (inv 1) (inv 2) + (2-p))

def quadIndex (_a _b _c _d : Nat) : Nat := 0
def additiveTrits (p : Pattern) : Array Nat := #[wins p]

def patternConfig (p : Pattern) : Config 4 :=
  ⟨Fast.cfgOfPatG 4 quadIndex (additiveTrits p),
    fun q i j => decide (i ≠ j) && edge p (min i.val j.val) (max i.val j.val) q.val⟩

def restrictConfig {m n : Nat} (c : Config n) (e : Fin m → Fin n) : Config m :=
  ⟨c.additive.comap e, fun q i j => c.close q (e i) (e j)⟩

def fn4 (l : List (Fin 4)) : Fin 4 → Fin 4 := fun i => l.getD i.val 0
def all4 : List (List (Fin 4)) := Fast.allOrders (List.finRange 4)
def reps2 : List (List (Fin 4)) := all4.filter fun l => decide (fn4 l 0 < fn4 l 1)
def sel23 : Fin 3 → Fin 4 := fun i => ⟨i.val, by omega⟩
def sel23' : Fin 3 → Fin 4 := fun i =>
  if i.val < 2 then ⟨i.val, by omega⟩ else 3

def squareCode (b : Block) (c : Config 4) : K :=
  (ksum (reps2.map fun l => entryAt b.expanded
    (pairFlag b (restrictConfig c (fn4 l ∘ sel23)) % (b.flags.size+1))
    (pairFlag b (restrictConfig c (fn4 l ∘ sel23')) % (b.flags.size+1)))).smul (1/12)

/-- The actual symmetrized objective plus ordinary flag squares.
There are no degree, sublaw, or near-optimality terms. -/
def score (blocks : Array Block) (p : Pattern) : K :=
  (K.ofRat ((wins p : Rat)/4)).add
    (ksum (blocks.toList.map fun b => squareCode b (patternConfig p)))

end Fast.Four
