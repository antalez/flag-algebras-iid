import Fast.Five.Config
import Fast.Five.Check

namespace Fast.Five

def bitNat (b : Bool) : Nat := if b then 1 else 0

def code3 (c : Config 3) (a b d : Fin 3) : Nat :=
  bitNat (c.close a b) + 2*bitNat (c.close a d) + 4*bitNat (c.close b d)

def code4 (c : Config 4) (a b d e : Fin 4) : Nat :=
  bitNat (c.close a b) + 2*bitNat (c.close a d) + 4*bitNat (c.close a e) +
  8*bitNat (c.close b d) + 16*bitNat (c.close b e) + 32*bitNat (c.close d e) +
  64*bitNat (c.additive.sb a b e d) + 128*bitNat (c.additive.sb a b d e)

/-- One root at position 0, followed by two sorted extensions. The missing-flag
index is the zero row just after the recorded flags. -/
def singletonFlag (b : Block) (c : Config 3) : Nat :=
  let p := bitNat (c.additive.lt 1 0) + bitNat (c.additive.lt 2 0)
  let inv : Nat → Fin 3 := fun k =>
    if k = p then 0 else Fin.ofNat 3 (1+k-bitNat (decide (p<k)))
  b.flags.toList.idxOf (3*code3 c (inv 0) (inv 1) (inv 2)+p)

/-- Three sorted roots at positions 0,1,2 and one extension at position 3. -/
def tripleFlag (b : Block) (c : Config 4) : Nat :=
  let ty := bitNat (c.close 0 1) + 2*bitNat (c.close 0 2) + 4*bitNat (c.close 1 2)
  if ty != b.ty then b.flags.size else
    let p := bitNat (c.additive.lt 0 3) + bitNat (c.additive.lt 1 3) + bitNat (c.additive.lt 2 3)
    let inv : Nat → Fin 4 := fun k =>
      if k = p then 3 else Fin.ofNat 4 (k-bitNat (decide (p<k)))
    b.flags.toList.idxOf (4*code4 c (inv 0) (inv 1) (inv 2) (inv 3)+(3-p))

end Fast.Five
