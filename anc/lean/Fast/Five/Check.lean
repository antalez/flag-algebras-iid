import Fast.Five.Basic

namespace Fast.Five

def ksum (xs : List K) : K := xs.foldl K.add K.zero

def lower (lo hi : Rat) (x : K) : Rat :=
  x.a + x.b * (if 0 ≤ x.b then lo else hi) +
  x.c * (if 0 ≤ x.c then lo*lo else hi*hi) +
  x.d * (if 0 ≤ x.d then lo*lo*lo else hi*hi*hi)

def upper (lo hi : Rat) (x : K) : Rat :=
  x.a + x.b * (if 0 ≤ x.b then hi else lo) +
  x.c * (if 0 ≤ x.c then hi*hi else lo*lo) +
  x.d * (if 0 ≤ x.d then hi*hi*hi else lo*lo*lo)

def absBound (lo hi : Rat) (x : K) : Rat := max (-(lower lo hi x)) (upper lo hi x)
def keq (x y : K) : Bool := x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d

structure Block where
  roots : Nat
  flagSize : Nat
  ty : Nat
  flags : Array Nat
  basis : Array (List (Nat × K))
  matrix : Array (Array K)
  expanded : Array (Array K)
  gram : Array (List Int)
  gramDen : Nat
  deriving Inhabited

def entryAt (a : Array (Array K)) (i j : Nat) : K := (a[i]?.getD #[])[j]?.getD K.zero

def dot (x y : List Int) : Int := (x.zipWith (· * ·) y).sum

def residual (b : Block) (i j : Nat) : K :=
  (entryAt b.matrix i j).sub (K.ofRat ((dot (b.gram[i]?.getD []) (b.gram[j]?.getD []) : Rat) /
    ((b.gramDen : Rat) * b.gramDen)))

def expandedEntry (b : Block) (i j : Nat) : K :=
  ksum ((b.basis[i]?.getD []).flatMap fun a => (b.basis[j]?.getD []).map fun c =>
    (a.2.mul (entryAt b.matrix a.1 c.1)).mul c.2)

def blockShape (b : Block) : Bool :=
  let d := b.flags.size
  let k := b.matrix.size
  decide (0 < k ∧ 0 < d ∧ 0 < b.gramDen ∧ b.roots < b.flagSize ∧ 2*b.flagSize-b.roots = 5) &&
  b.matrix.all (fun row => row.size == k) && b.basis.size == d &&
  b.basis.all (fun row => row.all (fun e => decide (e.1 < k))) &&
  b.expanded.size == d && b.expanded.all (fun row => row.size == d) &&
  b.gram.size == k && b.gram.all (fun row => row.length == k)

def psdRow (lo hi : Rat) (b : Block) (i : Nat) : Bool :=
  (List.range b.matrix.size).all (fun j => keq (entryAt b.matrix i j) (entryAt b.matrix j i)) &&
  decide (((List.range b.matrix.size).map (fun j => if j = i then 0 else
    absBound lo hi (residual b i j))).sum ≤ lower lo hi (residual b i i))

def expandedRow (b : Block) (i : Nat) : Bool :=
  (List.range b.flags.size).all (fun j => keq (entryAt b.expanded i j) (expandedEntry b i j))

def qEntry (b : Block) (a c : Nat) : K :=
  entryAt b.expanded (b.flags.toList.idxOf a) (b.flags.toList.idxOf c)

def square (b : Block) (p : Pattern) : K :=
  let rs := choose b.roots (List.range 5)
  let norm := rs.length * (choose (b.flagSize-b.roots) (List.range (5-b.roots))).length *
    (choose (b.flagSize-b.roots) (List.range (5-b.flagSize))).length
  (ksum (rs.flatMap fun roots =>
    if code p roots = b.ty then
      let rest := (List.range 5).filter (fun i => i ∉ roots)
      (choose (b.flagSize-b.roots) rest).flatMap fun a =>
        (choose (b.flagSize-b.roots) (rest.filter (fun i => i ∉ a))).map fun c =>
          qEntry b (flagCode p roots a) (flagCode p roots c)
    else [])).smul (1 / (norm : Rat))

/-- True selects z/2; false selects 2z. Only distinct i,z are used. -/
def below (p : Pattern) (i z : Nat) (half : Bool) : Bool :=
  if half then decide (i < z) && !(edge p i z)
  else decide (i < z) || edge p z i

def tail (p : Pattern) (half : Bool) (x : K) : K :=
  ksum ((List.range 5).map fun z =>
    let v := (List.range 5).filter (· != z)
    if v.all (fun i => below p i z half) then
      (x.sub (K.ofRat ((wins p v : Rat)/4))).smul (1/5)
    else K.zero)

def degree (p : Pattern) (nu : Array Rat) : K :=
  ksum ((List.range 5).flatMap fun z => ((List.range 5).filter (· != z)).map fun y =>
    let cl := (if edge p (min z y) (max z y) then 2 else 0) + (if z < y then 0 else 1)
    let v := (List.range 5).filter (· != y)
    ((K.ofRat ((wins p v : Rat)/4)).sub K.bstar).smul ((nu[cl]?.getD 0)/20))

def score (blocks : Array Block) (wHalf wTwice : Rat) (nu : Array Rat) (p : Pattern) (x : K) : K :=
  (K.ofRat (((quads 5).map (fun v => (wins p v : Rat))).sum/20)).add
    ((ksum (blocks.toList.map (fun b => square b p))).add
      (((tail p true x).smul wHalf).add (((tail p false x).smul wTwice).add (degree p nu))))

end Fast.Five
