import Fast.Cover
import Std.Data.HashMap

/-!
# Certificates of non-realizability (computable part)

A certificate for a pattern `P` on `n` points is a list of `(i, kind, weight)`: the strict inequality
of kind `kind` asserted by `P` on the `i`-th quadruple, with a positive integer weight. It is valid
if the weighted sum of the inequalities, written `∑_j coef_j x_j > 0`, has all suffix sums
`∑_{j ≥ k} coef_j ≤ 0`, which is impossible for `0 ≤ x_0 < x_1 < ...`.
-/

namespace Fast

abbrev Cert := List (Nat × Nat × Nat)

/-- Coefficient of `x_j` in `e1 = 2 x_d - x_a - x_b - x_c` (kind 0) or
`e2 = 2 x_c - x_a - x_b - x_d` (kind 1). -/
def coefE (kind : Nat) (q : Nat × Nat × Nat × Nat) (j : Nat) : Int :=
  let t := if kind = 0 then q.2.2.2 else q.2.2.1
  let o := if kind = 0 then q.2.2.1 else q.2.2.2
  (if j = t then 2 else 0) - (if j = q.1 then 1 else 0) - (if j = q.2.1 then 1 else 0)
    - (if j = o then 1 else 0)

/-- Sign with which the pattern asserts `e > 0`: `+1` if the trit says so, `-1` otherwise. -/
def signOf (kind s : Nat) : Int :=
  if kind = 0 then (if 1 ≤ s then 1 else -1) else (if s = 2 then 1 else -1)

def coefs (cs : List (Nat × Nat × Nat × Nat)) (P : Pat) (cert : Cert) (j : Nat) : Int :=
  (cert.map fun e =>
    (e.2.2 : Int) * signOf e.2.1 (P.getD e.1 0) * coefE e.2.1 (cs.getD e.1 (0, 0, 0, 0)) j).sum

def sufOk : List Int → Bool
  | [] => true
  | a :: t => sufOk t && decide (a + t.sum ≤ 0)

/-- `cs` is the list of quadruples of the `n` points (`combos n`), passed in precomputed. -/
def farkasOk (cs : List (Nat × Nat × Nat × Nat)) (n : Nat) (P : Pat) (cert : Cert) : Bool :=
  !cert.isEmpty &&
    cert.all (fun e => decide (0 < e.2.2) && decide (e.1 < cs.length) && decide (e.2.1 < 2)) &&
    sufOk ((List.range n).map (coefs cs P cert))

/-- Code of a pattern: `∑ P[i] 3^i`. -/
def patCode (P : Pat) : Nat := P.foldr (fun v acc => acc * 3 + v) 0

def parseTriples : List Nat → Cert
  | i :: k :: w :: rest => (i, k, w) :: parseTriples rest
  | _ => []

def parseCertLine (s : String) : Option ((Nat × Nat) × Cert) :=
  match (s.splitOn " ").filterMap String.toNat? with
  | n :: code :: rest => some ((n, code), parseTriples rest)
  | _ => none

def parseFarkas (s : String) : Std.HashMap (Nat × Nat) Cert :=
  (s.splitOn "\n").foldl (fun m line =>
    match parseCertLine line with
    | some (k, c) => m.insert k c
    | none => m) {}

/-- The pattern `P` on `n` points carries a valid certificate of non-realizability. -/
def excl (fm : Std.HashMap (Nat × Nat) Cert) (cs : List (Nat × Nat × Nat × Nat)) (n : Nat)
    (P : Pat) : Bool :=
  match fm[(n, patCode P)]? with
  | some cert => farkasOk cs n P cert
  | none => false

def R4 : Array Pat := #[#[0], #[1], #[2]]

/-- The patterns on `n` points all of whose restrictions lie in `R`, minus the excluded ones. -/
def levelR (fm : Std.HashMap (Nat × Nat) Cert) (n : Nat) (R : Array Pat) : Array Pat :=
  let cs := combos n
  (go (mkLevel n R) (fun P => !excl fm cs n P) n []).toArray

end Fast
