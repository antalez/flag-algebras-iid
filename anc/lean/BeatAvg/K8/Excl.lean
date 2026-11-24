import Fast.Farkas
import BeatAvg.K8.Search

/-!
# Certificates of non-realizability for packed patterns (definitions)
-/

namespace BeatAvg.K8

/-- A certificate packed in a number: the number of entries (4 bits), then for each entry the
position of the quadruple (7 bits), the kind (1 bit) and the weight (12 bits). -/
def unpackCert : Nat → Nat → Fast.Cert
  | 0, _ => []
  | k + 1, c =>
    (Nat.mod c 128, Nat.mod (Nat.shiftRight c 7) 2, Nat.mod (Nat.shiftRight c 8) 4096)
      :: unpackCert k (Nat.shiftRight c 20)

/-- The packed pattern `N` of `n` points (`len` trits) carries the valid certificate `c`. -/
def exclK (n len N c : Nat) : Bool :=
  Fast.farkasOk (ordQ n) n (unpackL N len 0).toArray (unpackCert (Nat.mod c 16) (Nat.shiftRight c 4))

/-- The first `k` fields of `w` bits of `xs` and of `wc` bits of `cs`, as pairs. -/
def unpackX (w wc : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | k + 1, xs, cs =>
    (Nat.mod xs (Nat.pow 2 w), Nat.mod cs (Nat.pow 2 wc))
      :: unpackX w wc k (Nat.shiftRight xs w) (Nat.shiftRight cs wc)

def lookupX : List (Nat × Nat × Nat × Nat) → Nat → Nat × Nat × Nat
  | [], _ => (0, 0, 0)
  | g :: gs, key => bif Nat.beq g.1 key then g.2 else lookupX gs key

def assoc : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | p :: l, k => bif Nat.beq p.1 k then some p.2 else assoc l k

def memN : List Nat → Nat → Bool
  | [], _ => false
  | a :: l, k => bif Nat.beq a k then true else memN l k

/-- All the stages of the join, from all the candidates of the first. -/
def extsAll (G : Grouped) (wb m T : Nat) : List Nat :=
  joinFrom G wb m T (m - 1) 1 (maskM (avoidT m 0)) (candsJ G wb m T 0)

/-- Level `n = m + 1`: every extension of the pattern `U` of `m` points found by the join is in
the group of `U` in `G'`, or carries a certificate. `sh` is the number of bits of `U`, `wb'` the
number of bits of an extension. -/
def chkLevel (G G' : Grouped) (X : List (Nat × Nat × Nat × Nat)) (wb wb' m len sh : Nat)
    (U : Nat) : Bool :=
  (extsAll G wb m U).all fun x =>
    memN (unpackE wb' (lookupG G' U).1 (lookupG G' U).2) x ||
      (match assoc (unpackX wb' 168 (lookupX X U).1 (lookupX X U).2.1 (lookupX X U).2.2) x with
        | some c => exclK (m + 1) len (Nat.add U (Nat.shiftLeft x sh)) c
        | none => false)

/-- The patterns of a grouped level, packed (`sh` bits for the prefix). -/
def allCodes (sh wb : Nat) : Grouped → List Nat
  | [] => []
  | g :: gs => (unpackE wb g.2.1 g.2.2).map (fun e => Nat.add g.1 (Nat.shiftLeft e sh))
      ++ allCodes sh wb gs

end BeatAvg.K8
