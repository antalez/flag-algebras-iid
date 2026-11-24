import Fast.Data
import Fast.Cert8

/-!
# The order-8 check (computable part)
-/

namespace Fast

def tabs8 : Tabs := tabsOf cert8

/-- The second point of the criterion is `Cbar0 = 100000 / 100000 = 1`; `δ = cbarE / 100000` is the
margin required there. -/
def cbarE : Int := 1

/-- A leaf passes if both inequalities are certified or the pattern is certified non-realizable. -/
def leafOk (P : Pat) : Bool :=
  checkBoth cert8.encLo cert8.encHi cert8.encM tabs8 100000 100000 cbarE (cfgOfPat P) ||
  excl fm combos8 8 P

/-- Number of failing leaves below the first-stage choices `lo ≤ i < hi` (testing). -/
def failRange (lo hi : Nat) : Nat :=
  (((cands (L8.stages.getD 0 ⟨#[], #[], #[]⟩) []).drop lo).take (hi - lo)).map (fun T =>
    Task.spawn fun _ => (go L8 (fun P => !leafOk P) (L8.n - 1) [T]).length)
    |>.foldl (fun a t => a + t.get) 0

end Fast

namespace Fast

/-- Timing helper: evaluate parts of the functional `k` times on the pattern `P`. -/
def benchPart (which : Nat) (k : Nat) (P : Pat) : Nat := Id.run do
  let c := cfgOfPat P
  let mut acc : Int := 0
  for _ in [0:k] do
    let z : Z4 :=
      match which with
      | 0 => Z4.ofInt (cntObj c)
      | 1 => zsum (repsSq.map fun l => sqZ tabs8 c (fnOf l))
      | 2 => zsum (repsDeg.map fun l => degU tabs8 c (fnOf l))
      | 3 => zsum (repsDeg.map fun l => degV tabs8 c (fnOf l))
      | 4 => zsum (repsThr.map fun l => thrU tabs8 c (fnOf l))
      | 5 => zsum (repsThr.map fun l => thrV tabs8 c (fnOf l))
      | _ => Z4.ofInt (repsSq.foldl (fun a l => a + Fflag tabs8.ft (c.comap (fnOf l ∘ first5))) 0)
    acc := acc + z.a
  return acc.natAbs % 1000

end Fast

namespace Fast

/-- The whole order-8 check: no leaf of the level-8 enumeration fails. -/
def check8 (_ : Unit) : Bool := goPar L8 (fun P => !leafOk P)

end Fast
