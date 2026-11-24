import BeatAvg.K8.TbF
import BeatAvg.K8.L7G
import BeatAvg.K8.Excl

/-!
# The order-8 check for the kernel (definitions)

For each pattern `T` of seven points in the level `D.G7`, every extension `x` found by the join
passes the leaf test (`leafOkF`, for `Cbar0 = 100000/100000` and margin `1/100000`), or the pattern
`T + 4^35 · x` of eight points carries a certificate of non-realizability.
-/

namespace BeatAvg.K8

/-- The pattern `N` of eight points carries a valid certificate of non-realizability. -/
def excl8 (N : Nat) : Bool :=
  match assoc D.X8 N with
  | some c => exclK 8 70 N c
  | none => false

def leaf8 (T x : Nat) : Bool :=
  leafOkF D.tb D.tf 100000 100000 1 T x || excl8 (Nat.add T (Nat.shiftLeft x 70))

/-- The leaves of the pattern `T` of seven points: the join with tries. -/
def leavesT (T : Nat) : List Nat :=
  joinFromT D.G7 40 7 T 6 1 (maskM (avoidT 7 0)) (candsJ D.G7 40 7 T 0)

def chk8 (T : Nat) : Bool := (leavesT T).all (leaf8 T)

/-- The patterns of seven points. -/
def codes7 : List Nat := allCodes 30 40 D.G7

/-- The check for the patterns `lo ≤ i < hi` of `codes7`. -/
def chkR (lo hi : Nat) : Bool := ((codes7.drop lo).take (hi - lo)).all chk8

end BeatAvg.K8

namespace BeatAvg.K8

/-! ### Pieces of the check

A pattern of seven points is addressed by its group `g` in `D.G7` and its index `j` in the group.
-/

def grp (g : Nat) : Nat × Nat × Nat := nth (0, 0, 0) D.G7 g

def T7 (g j : Nat) : Nat :=
  Nat.add (grp g).1 (Nat.shiftLeft (nth 0 (unpackE 40 (grp g).2.1 (grp g).2.2) j) 30)

/-- Leaves `lo ≤ i < hi` of the pattern `(g, j)`. -/
def chkT (g j lo hi : Nat) : Bool :=
  (((leavesT (T7 g j)).drop lo).take (hi - lo)).all (leaf8 (T7 g j))

/-- Leaves from `lo` on of the pattern `(g, j)`. -/
def chkD (g j lo : Nat) : Bool := ((leavesT (T7 g j)).drop lo).all (leaf8 (T7 g j))

/-- The patterns `a ≤ j < b` of the group `g`. -/
def chkJ (g a b : Nat) : Bool := (List.range' a (b - a)).all fun j => chkD g j 0

def chkG (g : Nat) : Bool := chkJ g 0 (grp g).2.1

/-- The groups `a ≤ g < b`. -/
def chkGs (a b : Nat) : Bool := (List.range' a (b - a)).all chkG

end BeatAvg.K8

namespace BeatAvg.K8

/-! ### Pieces by first-stage candidates

The join of a pattern of seven points is split along the candidates of its first stage: the piece
`chkC g j lo hi` follows the candidates `lo ≤ c < hi`, so it does its share of the search as well
as of the evaluation.
-/

def chkC (g j lo hi : Nat) : Bool :=
  (joinFromT D.G7 40 7 (T7 g j) 6 1 (maskM (avoidT 7 0))
    (((candsJ D.G7 40 7 (T7 g j) 0).drop lo).take (hi - lo))).all (leaf8 (T7 g j))

def chkCD (g j lo : Nat) : Bool :=
  (joinFromT D.G7 40 7 (T7 g j) 6 1 (maskM (avoidT 7 0))
    ((candsJ D.G7 40 7 (T7 g j) 0).drop lo)).all (leaf8 (T7 g j))

end BeatAvg.K8
