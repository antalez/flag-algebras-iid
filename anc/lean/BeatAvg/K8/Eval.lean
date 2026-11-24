import Fast.Tables
import BeatAvg.K8.Search

/-!
# Kernel-friendly evaluation of the order-8 functional on a packed pattern (definitions)

`N` is the packed pattern of eight sorted points (trits of `ordQ 8`). The four sums over canonical
arrangements are computed from tables compiled once from the lists of arrangements:

* the pattern code of each five-point subset (`codes`), from which flags and classes are read in
  packed tables;
* sum bits as tests `Nat.land H f = 0` on the one-hot form `H` of the pattern, where `f` is a set
  of forbidden (position, trit) pairs;
* numbers of `Z[r]` as packed fields with an offset, so that a sum of table entries is one addition
  of natural numbers per term.
-/

namespace BeatAvg.K8

open Fast (Z4)

/-! ### Compilation of arrangements (run once; the results are stored as literals) -/

def insertS (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insertS x l

def sortL : List Nat → List Nat
  | [] => []
  | x :: l => insertS x (sortL l)

/-- The increasing lists of five points among eight, in lexicographic order. -/
def subs5 : List (List Nat) :=
  (List.range 8).flatMap fun a => (List.range 8).flatMap fun b => (List.range 8).flatMap fun c =>
    (List.range 8).flatMap fun d => (List.range 8).filterMap fun e =>
      if a < b ∧ b < c ∧ c < d ∧ d < e then some [a, b, c, d, e] else none

/-- Position of a quadruple in the pattern of eight points. -/
def posQ8 (q : Nat × Nat × Nat × Nat) : Nat := (ordQ 8).idxOf q

/-- Bit offsets, in the packed pattern, of the five quadruples of the points `s` (increasing), in
the order of the quadruples of five points. -/
def quads5 (s : List Nat) : Nat × Nat × Nat × Nat × Nat :=
  let g := fun i => s.getD i 0
  (2 * posQ8 (g 0, g 1, g 2, g 3), 2 * posQ8 (g 0, g 1, g 2, g 4), 2 * posQ8 (g 0, g 1, g 3, g 4),
    2 * posQ8 (g 0, g 2, g 3, g 4), 2 * posQ8 (g 1, g 2, g 3, g 4))

def sub5Spec : List (Nat × Nat × Nat × Nat × Nat) := subs5.map quads5

/-- The sum bit `x_a + x_b + x_c < 2 x_d` of a sorted sample, as (position of a quadruple, set of
the trits for which it holds). -/
def sbAtom (a b c d : Nat) : Nat × Nat :=
  let x := min a (min b c)
  let z := max a (max b c)
  let y := a + b + c - x - z
  if x < y ∧ y < z then
    if z < d then (posQ8 (x, y, z, d), 6)
    else if y < d ∧ d < z then (posQ8 (x, y, d, z), 4)
    else (0, 0)
  else (0, 0)

/-- Forbidden bits of the one-hot pattern for the atom to hold / to fail. -/
def forbT (a : Nat × Nat) : Nat := Nat.shiftLeft (7 - a.2) (3 * a.1)
def forbF (a : Nat × Nat) : Nat := Nat.shiftLeft a.2 (3 * a.1)

def pairIdx (p q : Nat) : Nat := p * (9 - p) / 2 + (q - p - 1)

/-- Square term: offsets of the two five-point subsets in `codes` and of the root pairs in the
flag table. -/
def compSq (l : List Nat) : Nat × Nat × Nat × Nat :=
  let g := fun i => l.getD i 0
  let sA := sortL [g 0, g 1, g 2, g 3, g 4]
  let sB := sortL [g 0, g 1, g 5, g 6, g 7]
  (8 * subs5.idxOf sA, 9 * pairIdx (sA.idxOf (g 0)) (sA.idxOf (g 1)),
    8 * subs5.idxOf sB, 9 * pairIdx (sB.idxOf (g 0)) (sB.idxOf (g 1)))

def bitAt (m t : Nat) : Nat := Nat.mod (Nat.shiftRight m t) 2

/-- Degree term: offset of the subset, offset of the rank of the root in the class table, bit
offset of the quadruple of the root and the three other points, and the values of `s4C` for the
three trits of that quadruple (four bits each). -/
def compDeg (l : List Nat) : Nat × Nat × Nat × Nat :=
  let g := fun i => l.getD i 0
  let s := sortL [g 0, g 1, g 2, g 3, g 4]
  let a1 := sbAtom (g 0) (g 5) (g 6) (g 7)
  let a2 := sbAtom (g 5) (g 6) (g 7) (g 0)
  let sv := fun t => 3 * bitAt a1.2 t + bitAt a2.2 t
  (8 * subs5.idxOf s, 8 * s.idxOf (g 0),
    2 * posQ8 (let q := sortL [g 0, g 5, g 6, g 7]; (q.getD 0 0, q.getD 1 0, q.getD 2 0, q.getD 3 0)),
    sv 0 + 16 * sv 1 + 256 * sv 2)

/-- The two atoms of a degree term read the quadruple recorded by `compDeg`. -/
def compDegOk (l : List Nat) : Bool :=
  let g := fun i => l.getD i 0
  let a1 := sbAtom (g 0) (g 5) (g 6) (g 7)
  let a2 := sbAtom (g 5) (g 6) (g 7) (g 0)
  let p := (compDeg l).2.2.1
  (a1.2 == 0 || 2 * a1.1 == p) && (a2.2 == 0 || 2 * a2.1 == p)

def tripI (t : Nat) : Nat := if t % 4 = 3 then 1 else 0
def tripJ (t : Nat) : Nat := if t % 4 = 0 ∨ t % 4 = 1 then 1 else 2
def tripK (t : Nat) : Nat := if t % 4 = 0 then 2 else 3

/-- Forbidden bits for "the point at position `p` lies below the threshold `θ`". -/
def belowF (l : List Nat) (θ p : Nat) : Nat :=
  let g := fun i => l.getD i 0
  if θ < 4 then forbT (sbAtom (g p) (g (tripI θ)) (g (tripK θ)) (g (tripJ θ)))
  else if g p < g (tripK θ) then 0
  else forbF (sbAtom (g (tripI θ)) (g (tripJ θ)) (g (tripK θ)) (g p))

/-- Threshold term: forbidden bits for "type 0", then for each threshold the forbidden bits of
"type 0, fresh points succeed, all below", "type 0, fresh points succeed, target below" and
"type 0, all below". -/
def compThr (l : List Nat) : Nat × List (Nat × Nat × Nat) :=
  let g := fun i => l.getD i 0
  let fR := forbF (sbAtom (g 0) (g 1) (g 2) (g 3))
  let fS := forbT (sbAtom (g 4) (g 5) (g 6) (g 7))
  (fR, (List.range 8).map fun θ =>
    let ab := Nat.lor (Nat.lor (belowF l θ 4) (belowF l θ 5)) (Nat.lor (belowF l θ 6) (belowF l θ 7))
    (Nat.lor fR (Nat.lor fS ab), Nat.lor fR (Nat.lor fS (belowF l θ 7)), Nat.lor fR ab))

/-- Objective term: forbidden bits for "the first four points succeed". -/
def compObj (l : List Nat) : Nat :=
  forbT (sbAtom (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0))

/-! ### Tables -/

/-- Tables of the evaluation. Numbers of `Z[r]` are stored as fields `value + off`. -/
structure Tb where
  /-- positions of the quadruples of the five-point subsets -/
  sub5 : List (Nat × Nat × Nat × Nat × Nat)
  sq : List (Nat × Nat × Nat × Nat)
  deg : List (Nat × Nat × Nat × Nat)
  thr : List (Nat × List (Nat × Nat × Nat))
  obj : List Nat
  /-- flags: 9 bits for each (code, root pair) -/
  ftP : Nat
  /-- classes: 8 bits for each (code, rank of the root) -/
  ctP : Nat
  /-- rows of `Dn · Q` in a tree of fanout 7; an entry has four fields of `wQ` bits -/
  QT : List (List (List Nat))
  wQ : Nat
  offQ : Nat
  /-- degree entries `(class, s)`, one number for each class in a tree of fanout 13: eight
  fields of `wD` bits, `U` then `V` -/
  DT : List (List Nat)
  wD : Nat
  offD : Nat
  /-- threshold entries, for each threshold: eight fields of `wT` bits -/
  TT : List (Nat × Nat × Nat)
  wT : Nat
  offT : Nat
  Dn : Int
  encLo : Int
  encHi : Int
  encM : Nat

/-! ### Evaluation -/

/-- One-hot form of the first `k` trits: bit `3 i + t` is set iff trit `i` is `t`. -/
def hotN : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, N => Nat.add (Nat.shiftLeft 1 (Nat.mod N 4)) (Nat.mul 8 (hotN k (Nat.div N 4)))

def hot (N : Nat) : Nat := hotN 70 N

def trS (N s : Nat) : Nat := Nat.mod (Nat.shiftRight N s) 4

def code5 (N : Nat) (ps : Nat × Nat × Nat × Nat × Nat) : Nat :=
  Nat.add (trS N ps.1) (Nat.mul 3 (Nat.add (trS N ps.2.1) (Nat.mul 3 (Nat.add (trS N ps.2.2.1)
    (Nat.mul 3 (Nat.add (trS N ps.2.2.2.1) (Nat.mul 3 (trS N ps.2.2.2.2))))))))

/-- The codes of the 56 five-point subsets, eight bits each. -/
def codes (N : Nat) : List (Nat × Nat × Nat × Nat × Nat) → Nat
  | [] => 0
  | ps :: l => Nat.add (code5 N ps) (Nat.mul 256 (codes N l))

def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth d l n

def flagAt (ftP C o q : Nat) : Nat :=
  Nat.mod (Nat.shiftRight ftP (Nat.add (Nat.mul 90 (Nat.mod (Nat.shiftRight C o) 256)) q)) 512

def rowQ (QT : List (List (List Nat))) (f : Nat) : Nat :=
  nth 0 (nth [] (nth [] QT (Nat.div f 49)) (Nat.mod (Nat.div f 7) 7)) (Nat.mod f 7)

/-- The entry `(i, j)` of the packed table of `Dn · Q`. -/
def entQ (t : Tb) (i j : Nat) : Nat :=
  Nat.mod (Nat.shiftRight (rowQ t.QT i) (Nat.mul (Nat.mul 4 t.wQ) j)) (Nat.pow 2 (Nat.mul 4 t.wQ))

/-- The entry `(class, s)` of the packed degree table. -/
def entD (t : Tb) (c s : Nat) : Nat :=
  Nat.mod (Nat.shiftRight (nth 0 (nth [] t.DT (Nat.div c 13)) (Nat.mod c 13))
    (Nat.mul (Nat.mul 8 t.wD) s)) (Nat.pow 2 (Nat.mul 8 t.wD))

def clsAt (ctP C o q : Nat) : Nat :=
  Nat.mod (Nat.shiftRight ctP (Nat.add (Nat.mul 40 (Nat.mod (Nat.shiftRight C o) 256)) q)) 256

def sqEnt (t : Tb) (C : Nat) (e : Nat × Nat × Nat × Nat) : Nat :=
  entQ t (flagAt t.ftP C e.1 e.2.1) (flagAt t.ftP C e.2.2.1 e.2.2.2)

def degEnt (t : Tb) (N C : Nat) (e : Nat × Nat × Nat × Nat) : Nat :=
  entD t (clsAt t.ctP C e.1 e.2.1) (Nat.mod (Nat.shiftRight e.2.2.2 (Nat.mul 4 (trS N e.2.2.1))) 16)

def sqAcc (t : Tb) (C : Nat) : List (Nat × Nat × Nat × Nat) → Nat → Nat
  | [], acc => acc
  | e :: l, acc => sqAcc t C l (Nat.add acc (sqEnt t C e))

def degAcc (t : Tb) (N C : Nat) : List (Nat × Nat × Nat × Nat) → Nat → Nat
  | [], acc => acc
  | e :: l, acc => degAcc t N C l (Nat.add acc (degEnt t N C e))

def sel (H f x z : Nat) : Nat := bif Nat.beq (Nat.land H f) 0 then x else z

/-- One arrangement with roots of type 0: for each threshold, three entries or the zero entry. -/
def thrTh (H z : Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Nat → Nat
  | f :: fs, e :: es, acc =>
    thrTh H z fs es (Nat.add (Nat.add (Nat.add acc (sel H f.1 e.1 z)) (sel H f.2.1 e.2.1 z))
      (sel H f.2.2 e.2.2 z))
  | _, _, acc => acc

def thrAcc (t : Tb) (H z z24 : Nat) : List (Nat × List (Nat × Nat × Nat)) → Nat → Nat
  | [], acc => acc
  | e :: l, acc =>
    thrAcc t H z z24 l (bif Nat.beq (Nat.land H e.1) 0 then thrTh H z e.2 t.TT acc
      else Nat.add acc z24)

def objCnt (H : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | f :: l, acc => objCnt H l (sel H f (Nat.add acc 1) acc)

/-- Field `k` of width `w`, minus the offset `o`. -/
def fld (acc w k : Nat) (o : Nat) : Int :=
  Int.sub (Int.ofNat (Nat.mod (Nat.shiftRight acc (Nat.mul w k)) (Nat.pow 2 w))) (Int.ofNat o)

def decZ (acc w k o : Nat) : Z4 :=
  ⟨fld acc w k o, fld acc w (k + 1) o, fld acc w (k + 2) o, fld acc w (k + 3) o⟩

/-- The zero entry with eight fields. -/
def zero8 (w off : Nat) : Nat :=
  (List.range 8).foldl (fun a k => Nat.add a (Nat.shiftLeft off (Nat.mul w k))) 0

/-- `(U, V)` with `4 · Dn · LamR(x) = U + 4x · V`. -/
def lamUV (t : Tb) (N : Nat) : Z4 × Z4 :=
  let H := hot N
  let C := codes N t.sub5
  let sq := sqAcc t C t.sq 0
  let dg := degAcc t N C t.deg 0
  let z := zero8 t.wT t.offT
  let th := thrAcc t H z (Nat.mul 24 z) t.thr 0
  let ob := objCnt H t.obj 0
  let SQ := decZ sq t.wQ 0 (Nat.mul 560 t.offQ)
  let DU := decZ dg t.wD 0 (Nat.mul 840 t.offD)
  let DV := decZ dg t.wD 4 (Nat.mul 840 t.offD)
  let TU := decZ th t.wT 0 (Nat.mul 6720 t.offT)
  let TV := decZ th t.wT 4 (Nat.mul 6720 t.offT)
  ((Fast.Z4.ofInt (576 * t.Dn * (ob : Int))).add
      ((Z4.smul 288 SQ).add ((Z4.smul 48 DU).add (Z4.smul 144 TU))),
    (Z4.smul 48 DV).add (Z4.smul 144 TV))

/-- Both inequalities for the packed pattern `N`: `Λ(B*) ≤ B*` and `Λ(p/q) ≤ (p - e)/q`. -/
def leafOk (t : Tb) (p q e : Int) (N : Nat) : Bool :=
  Z4.nonneg t.encLo t.encHi t.encM
      (((Z4.smul (40320 * t.Dn) Fast.b4).sub (lamUV t N).1).sub (Fast.b4.mul (lamUV t N).2)) &&
    Z4.nonneg t.encLo t.encHi t.encM
      (((Fast.Z4.ofInt (4 * t.Dn * 40320 * (p - e))).sub (Z4.smul q (lamUV t N).1)).sub
        (Z4.smul (4 * p) (lamUV t N).2))

end BeatAvg.K8
