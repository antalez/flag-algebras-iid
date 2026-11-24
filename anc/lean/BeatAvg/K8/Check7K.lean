import BeatAvg.K8.L56
import BeatAvg.K8.L7G
import BeatAvg.K8.L7X
import BeatAvg.K8.Excl

/-!
# The level checks for the kernel (definitions)
-/

namespace BeatAvg.K8

def chk5 : Nat → Bool := chkLevel D.G4 D.G5 D.X5 2 8 4 5 2
def chk6 : Nat → Bool := chkLevel D.G5 D.G6 D.X6 8 20 5 15 10
def chk7 : Nat → Bool := chkLevel D.G6 D.G7 D.X7 20 40 6 35 30

/-- The patterns `lo ≤ i < hi` of six points. -/
def lev7T (lo hi : Nat) : Bool := (((allCodes 10 20 D.G6).drop lo).take (hi - lo)).all chk7

/-- The patterns of six points from `lo` on. -/
def lev7D (lo : Nat) : Bool := ((allCodes 10 20 D.G6).drop lo).all chk7

end BeatAvg.K8
