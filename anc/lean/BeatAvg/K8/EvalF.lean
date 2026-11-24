import BeatAvg.K8.Eval

/-!
# Evaluation specialised to a prefix (definitions)

A leaf is `N = T + 4^35 · x`: `T` packs the pattern of the first seven points, `x` the trits of the
quadruples containing the last point. Many leaves share `T`. The kernel caches the value of every
closed term, so a sub-term that mentions `T` and literals only is evaluated once for all the leaves
of a prefix. The evaluation below is arranged so that the work done per leaf is small:

* the terms of the square and degree sums in which only one five-point subset contains the last
  point are grouped by that subset; the sum of a group is a function of the four new trits of the
  subset, selected by `pick3` so that the group sum is a closed term;
* the threshold conditions are grouped by their part on the new trits; the part on the old trits
  is evaluated once per prefix.

`lamUVF t f T x` is equal to `lamUV t (T + 4^35 · x)` (`EvalFSound.lean`).
-/

namespace BeatAvg.K8

open Fast (Z4)

/-- Tables grouped for the specialised evaluation. -/
structure Tf where
  /-- the subsets containing the last point: offset in the codes, bit offsets in `x` of the four
  new trits -/
  sNew : List (Nat × Nat × Nat × Nat × Nat)
  /-- for each of them, the bit offset in `x` of the quadruple of the complement and the last
  point -/
  kq : List Nat
  /-- square terms with exactly one new subset, by that subset -/
  sqG : List (List (Nat × Nat × Nat × Nat))
  /-- degree terms with a new subset, by that subset -/
  degG : List (List (Nat × Nat × Nat × Nat))
  /-- square terms with two new subsets -/
  sqR : List (Nat × Nat × Nat × Nat)
  /-- degree terms with an old subset, by the new quadruple (bit offset in `x`) -/
  degQ : List (Nat × List (Nat × Nat × Nat × Nat))
  /-- threshold conditions by their new part: (new part, number of items, old parts and entries) -/
  thrG : List (Nat × Nat × List (Nat × Nat))
  objO : List Nat
  objN : List Nat

def sumL {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => Nat.add (f a) (sumL f l)

/-- `f τ` for a trit `τ`, by cases, so that the result is `f` applied to a literal. -/
def pick3 {α : Type} (τ : Nat) (f : Nat → α) : α :=
  bif Nat.beq τ 0 then f 0 else bif Nat.beq τ 1 then f 1 else f 2

def digit (C o : Nat) : Nat := Nat.mod (Nat.shiftRight C o) 256

def flagC (ftP code q : Nat) : Nat :=
  Nat.mod (Nat.shiftRight ftP (Nat.add (Nat.mul 90 code) q)) 512

def clsC (ctP code q : Nat) : Nat :=
  Nat.mod (Nat.shiftRight ctP (Nat.add (Nat.mul 40 code) q)) 256

/-- The code of a new subset from the code of its old quadruple and its four new trits. -/
def codeOf (CT S8 a b c d : Nat) : Nat :=
  Nat.add (digit CT S8) (Nat.mul 3 (Nat.add a (Nat.mul 3 (Nat.add b (Nat.mul 3
    (Nat.add c (Nat.mul 3 d)))))))

/-- A square entry in which the subset at offset `S8` has the code `code`; the other codes are
read in the codes of the prefix. -/
def sqEntO (t : Tb) (CT S8 code : Nat) (e : Nat × Nat × Nat × Nat) : Nat :=
  entQ t (flagC t.ftP (bif Nat.beq e.1 S8 then code else digit CT e.1) e.2.1)
    (flagC t.ftP (bif Nat.beq e.2.2.1 S8 then code else digit CT e.2.2.1) e.2.2.2)

/-- A degree entry in which the subset at offset `S8` has the code `code`, and the trit of a new
quadruple is `τ`. -/
def degEntO (t : Tb) (T CT S8 code τ : Nat) (e : Nat × Nat × Nat × Nat) : Nat :=
  entD t (clsC t.ctP (bif Nat.beq e.1 S8 then code else digit CT e.1) e.2.1)
    (Nat.mod (Nat.shiftRight e.2.2.2
      (Nat.mul 4 (bif Nat.ble 70 e.2.2.1 then τ else trS T e.2.2.1))) 16)

def pick4 {α : Type} (x : Nat) (s : Nat × Nat × Nat × Nat × Nat) (f : Nat → Nat → Nat → Nat → α) : α :=
  pick3 (trS x s.2.1) fun a => pick3 (trS x s.2.2.1) fun b => pick3 (trS x s.2.2.2.1) fun c =>
    pick3 (trS x s.2.2.2.2) fun d => f a b c d

def sqLeaf (t : Tb) (CT S8 : Nat) (g : List (Nat × Nat × Nat × Nat)) (a b c d : Nat) : Nat :=
  sumL (sqEntO t CT S8 (codeOf CT S8 a b c d)) g

def degLeaf (t : Tb) (T CT S8 : Nat) (g : List (Nat × Nat × Nat × Nat)) (a b c d τ : Nat) : Nat :=
  sumL (degEntO t T CT S8 (codeOf CT S8 a b c d) τ) g

def sqNew (t : Tb) (CT x : Nat) : List (Nat × Nat × Nat × Nat × Nat) → List (List (Nat × Nat × Nat × Nat)) → Nat
  | s :: ss, g :: gs => Nat.add (pick4 x s (sqLeaf t CT s.1 g)) (sqNew t CT x ss gs)
  | _, _ => 0

def degNew (t : Tb) (T CT x : Nat) :
    List (Nat × Nat × Nat × Nat × Nat) → List Nat → List (List (Nat × Nat × Nat × Nat)) → Nat
  | s :: ss, k :: ks, g :: gs =>
    Nat.add (pick4 x s fun a b c d => pick3 (trS x k) (degLeaf t T CT s.1 g a b c d))
      (degNew t T CT x ss ks gs)
  | _, _, _ => 0

def degOld (t : Tb) (T CT x : Nat) : List (Nat × List (Nat × Nat × Nat × Nat)) → Nat
  | [] => 0
  | g :: gs =>
    Nat.add (pick3 (trS x g.1) fun τ => sumL (degEntO t T CT 1000 0 τ) g.2) (degOld t T CT x gs)

/-- Codes of the new subsets, without the old trit: `3 · (τ₁ + 3 τ₂ + 9 τ₃ + 27 τ₄)` at the offset
of the subset. -/
def codesX (x : Nat) : List (Nat × Nat × Nat × Nat × Nat) → Nat
  | [] => 0
  | s :: ss =>
    Nat.add (Nat.shiftLeft (Nat.mul 3 (Nat.add (trS x s.2.1) (Nat.mul 3 (Nat.add (trS x s.2.2.1)
      (Nat.mul 3 (Nat.add (trS x s.2.2.2.1) (Nat.mul 3 (trS x s.2.2.2.2)))))))) s.1)
      (codesX x ss)

/-- The old part of the threshold groups: for each group, the sum of the entries whose old
condition holds (the zero entry for the others), and the sum when the new condition fails. -/
def thrPrep (HT z : Nat) : List (Nat × Nat × List (Nat × Nat)) → List (Nat × Nat × Nat)
  | [] => []
  | g :: l => (g.1, sumL (fun it => sel HT it.1 it.2 z) g.2.2, Nat.mul g.2.1 z) :: thrPrep HT z l

def thrLive : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | p :: l => bif Nat.beq p.2.1 p.2.2 then thrLive l else p :: thrLive l

def thrDead : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | p :: l => bif Nat.beq p.2.1 p.2.2 then Nat.add p.2.2 (thrDead l) else thrDead l

def thrRun (Hx : Nat) : List (Nat × Nat × Nat) → Nat → Nat
  | [], acc => acc
  | p :: l, acc => thrRun Hx l (Nat.add acc (sel Hx p.1 p.2.1 p.2.2))

/-- `(U, V)` for the leaf `T + 4^35 · x`. -/
def lamUVF (t : Tb) (f : Tf) (T x : Nat) : Z4 × Z4 :=
  let HT := hotN 35 T
  let Hx := hotN 35 x
  let CT := codes T t.sub5
  let C := Nat.add CT (codesX x f.sNew)
  let sq := Nat.add (sqNew t CT x f.sNew f.sqG) (sumL (sqEnt t C) f.sqR)
  let dg := Nat.add (degNew t T CT x f.sNew f.kq f.degG) (degOld t T CT x f.degQ)
  let z := zero8 t.wT t.offT
  let th := thrRun Hx (thrLive (thrPrep HT z f.thrG)) (thrDead (thrPrep HT z f.thrG))
  let ob := Nat.add (objCnt HT f.objO 0) (objCnt Hx f.objN 0)
  let SQ := decZ sq t.wQ 0 (Nat.mul 560 t.offQ)
  let DU := decZ dg t.wD 0 (Nat.mul 840 t.offD)
  let DV := decZ dg t.wD 4 (Nat.mul 840 t.offD)
  let TU := decZ th t.wT 0 (Nat.mul 6720 t.offT)
  let TV := decZ th t.wT 4 (Nat.mul 6720 t.offT)
  ((Fast.Z4.ofInt (576 * t.Dn * (ob : Int))).add
      ((Z4.smul 288 SQ).add ((Z4.smul 48 DU).add (Z4.smul 144 TU))),
    (Z4.smul 48 DV).add (Z4.smul 144 TV))

def leafOkF (t : Tb) (f : Tf) (p q e : Int) (T x : Nat) : Bool :=
  Z4.nonneg t.encLo t.encHi t.encM
      (((Z4.smul (40320 * t.Dn) Fast.b4).sub (lamUVF t f T x).1).sub
        (Fast.b4.mul (lamUVF t f T x).2)) &&
    Z4.nonneg t.encLo t.encHi t.encM
      (((Fast.Z4.ofInt (4 * t.Dn * 40320 * (p - e))).sub (Z4.smul q (lamUVF t f T x).1)).sub
        (Z4.smul (4 * p) (lamUVF t f T x).2))

/-! ### Specification of the grouped tables -/

/-- Offsets (in the codes) of the subsets containing the last point, as a set of bits. -/
def newMask : Nat := (subs5.foldr (fun s acc => Nat.add (bif s.contains 7 then 1 else 0)
  (Nat.mul 2 acc)) 0)

/-- The subset at offset `o` contains the last point. -/
def isNewS (o : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight newMask (Nat.div o 8)) 2) 1

/-- Key of a square entry: the offset of its only new subset, or `1000` if both are new. -/
def sqKey (e : Nat × Nat × Nat × Nat) : Nat :=
  bif isNewS e.1 then (bif isNewS e.2.2.1 then 1000 else e.1) else e.2.2.1

/-- Key of a degree entry: the offset of its subset if new, else `2000 +` the bit offset of its
quadruple. -/
def degKey (e : Nat × Nat × Nat × Nat) : Nat := bif isNewS e.1 then e.1 else Nat.add 2000 e.2.2.1

/-- The subsets containing the last point, from the table of positions (offsets from `o`): offset
in the codes and bit offsets in `x` of the four new trits. A subset is new iff its second position
is beyond the prefix. -/
def sNewSpec : List (Nat × Nat × Nat × Nat × Nat) → Nat → List (Nat × Nat × Nat × Nat × Nat)
  | [], _ => []
  | ps :: l, o =>
    bif Nat.ble 70 ps.2.1 then
      (o, ps.2.1 - 70, ps.2.2.1 - 70, ps.2.2.2.1 - 70, ps.2.2.2.2 - 70) :: sNewSpec l (o + 8)
    else sNewSpec l (o + 8)

/-- The threshold items: forbidden bits and entry. -/
def thrFlat (t : Tb) : List (Nat × Nat) :=
  t.thr.flatMap fun e => (e.2.zip t.TT).flatMap fun p =>
    [(p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)]

def lowM : Nat := 2 ^ 105 - 1

/-- The grouped tables, computed from the tables of the evaluation. The literal tables are checked
against this specification by the kernel. -/
def tfSpec (t : Tb) (kq : List Nat) (quads : List Nat) (masks : List Nat) : Tf where
  sNew := sNewSpec t.sub5 0
  kq := kq
  sqG := (sNewSpec t.sub5 0).map fun s => t.sq.filter fun e => Nat.beq (sqKey e) s.1
  degG := (sNewSpec t.sub5 0).map fun s => t.deg.filter fun e => Nat.beq (degKey e) s.1
  sqR := t.sq.filter fun e => Nat.beq (sqKey e) 1000
  degQ := quads.map fun k => (k - 70, t.deg.filter fun e => Nat.beq (degKey e) (Nat.add 2000 k))
  thrG := masks.map fun m =>
    (m, ((thrFlat t).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).length,
      ((thrFlat t).filter fun it => Nat.beq (Nat.shiftRight it.1 105) m).map fun it =>
        (Nat.land it.1 lowM, it.2))
  objO := (t.obj.filter fun f => Nat.beq (Nat.shiftRight f 105) 0)
  objN := (t.obj.filter fun f => !(Nat.beq (Nat.shiftRight f 105) 0)).map fun f =>
    Nat.shiftRight f 105

end BeatAvg.K8
