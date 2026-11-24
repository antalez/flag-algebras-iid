import Fast.Tables
import Fast.Cert8Data

/-!
# The order-8 certificate: data, `Q = W Y W^T`, tables (computable part)

The data are Lean numerals (`Fast/Cert8Data.lean`), so that the kernel can evaluate the checks of
`Fast/Psd.lean`. The functions used by those checks are structurally recursive on lists.
-/

namespace Fast

/-! ### Packed rows -/

/-- The `n` lowest fields of width `w` of `x`. -/
def unpackN (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => x % 2 ^ w :: unpackN w n (x / 2 ^ w)

/-- A signed field. -/
def sInt (w v : Nat) : Int := (v : Int) - ((2 ^ (w - 1) : Nat) : Int)

def kOf (n0 n1 n2 n3 d : Int) : K := ⟨(n0 : Rat) / d, (n1 : Rat) / d, (n2 : Rat) / d, (n3 : Rat) / d⟩

def kOfList : List Int → K
  | [n0, n1, n2, n3, d] => kOf n0 n1 n2 n3 d
  | _ => K.zero

/-- The element of `K` in the five lowest fields of `x` (four numerators and a denominator). -/
def kOfP (w x : Nat) : K := kOfList ((unpackN w 5 x).map (sInt w))

/-- `n` elements of `K` packed in `x`. -/
def kRow (w : Nat) : Nat → Nat → List K
  | 0, _ => []
  | n + 1, x => kOfP w x :: kRow w n (x / 2 ^ (5 * w))

/-- Replace the entries at the given (increasing) positions; the row starts at position `b`. -/
def patchRow : Nat → List K → List (Nat × K) → List K
  | _, [], _ => []
  | b, x :: xs, os =>
    match os with
    | [] => x :: xs
    | o :: os' => if o.1 = b then o.2 :: patchRow (b + 1) xs os' else x :: patchRow (b + 1) xs os

/-! ### The certificate -/

structure Cert8 where
  ft : Array Nat
  ct : Array Nat
  /-- sparse rows of `W` (300 rows, columns `< 255`) -/
  W : Array (List (Nat × K))
  /-- rows of `Y` (255 × 255) -/
  Yr : List (List K)
  /-- columns of the integer factor `G` (255 × 255), scaled by `2^gT` -/
  Gc : List (List Int)
  gT : Nat
  lo : Array K
  hi : Array K
  w1 : Array K
  w2 : Array K
  cbarP : Int
  cbarQ : Int
  Dn : Int
  encLo : Int
  encHi : Int
  encM : Nat
  B : Int

/-- The order-8 certificate. -/
def cert8 : Cert8 where
  ft := D8.ft.toArray
  ct := D8.ct.toArray
  W := (D8.wRows.map fun row => row.map fun e => (e.1, kOfP D8.wS e.2)).toArray
  Yr := List.zipWith
    (fun x big => patchRow 0 (kRow D8.wY 255 x) (big.map fun e => (e.1, kOfP D8.wB e.2)))
    D8.yRows D8.yBig
  Gc := D8.gCols.map fun x => (unpackN D8.wG 255 x).map (sInt D8.wG)
  gT := D8.gT
  lo := (D8.lo.map (kOfP D8.wS)).toArray
  hi := (D8.hi.map (kOfP D8.wS)).toArray
  w1 := (D8.w1.map (kOfP D8.wS)).toArray
  w2 := (D8.w2.map (kOfP D8.wS)).toArray
  cbarP := D8.cbarP
  cbarQ := D8.cbarQ
  Dn := D8.Dn
  encLo := D8.encLo
  encHi := D8.encHi
  encM := D8.encM
  B := D8.B

def ksum (l : List K) : K := l.foldl K.add K.zero

/-- Entry `(a, b)` of a matrix given by rows. -/
def yAt (Yr : List (List K)) (a b : Nat) : K := (Yr.getD a []).getD b K.zero

/-- Entry of `W Y W^T` for two sparse rows of `W`. -/
def QKw (Yr : List (List K)) (wi wj : List (Nat × K)) : K :=
  ksum (wi.flatMap fun e => wj.map fun e' => (e.2.mul (yAt Yr e.1 e'.1)).mul e'.2)

/-- Entry of `Q = W Y W^T`. -/
def QK (c : Cert8) (i j : Nat) : K := QKw c.Yr (c.W.getD i []) (c.W.getD j [])

/-- Entry `k = 300 i + j` of the table of `Dn · Q`. -/
def qzAt (c : Cert8) (k : Nat) : Z4 := (QK c (k / 300) (k % 300)).toZ4 c.Dn

def qzFn (c : Cert8) (k : Fin 90000) : Z4 := qzAt c k.val

/-- The integer tables of the certificate. -/
def tabsOf (c : Cert8) : Tabs where
  ft := c.ft
  ct := c.ct
  QZ := Array.ofFn (qzFn c)
  loZ := c.lo.map (K.toZ4 c.Dn)
  hiZ := c.hi.map (K.toZ4 c.Dn)
  w1Z := c.w1.map (K.toZ4 c.Dn)
  w2Z := c.w2.map (K.toZ4 c.Dn)
  Dn := c.Dn

/-- Row `i` of `Dn · Q` is integral. -/
def intRow (c : Cert8) (i : Nat) : Bool :=
  c.W.toList.all fun wj => (QKw c.Yr (c.W.getD i []) wj).integralAt c.Dn

/-- All numbers of the tables become integers after multiplication by `Dn`. -/
def integralOk (c : Cert8) : Bool :=
  (List.range 300).all (intRow c) &&
    c.lo.toList.all (K.integralAt c.Dn) && c.hi.toList.all (K.integralAt c.Dn) &&
    c.w1.toList.all (K.integralAt c.Dn) && c.w2.toList.all (K.integralAt c.Dn)

end Fast
