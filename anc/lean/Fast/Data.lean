import Fast.Farkas

/-!
# Data: certificates of non-realizability and the levels (top-level constants)

Top-level constants are computed once when the library is loaded and are then shared without
reference counting, which matters for the parallel enumeration.
-/

namespace Fast

def farkasStr : String := include_str "../data/farkas.txt"

def fm : Std.HashMap (Nat × Nat) Cert := parseFarkas farkasStr

def R5 : Array Pat := levelR fm 5 R4
def R6 : Array Pat := levelR fm 6 R5
def R7 : Array Pat := levelR fm 7 R6

def L5 : Level := mkLevel 5 R4
def L6 : Level := mkLevel 6 R5
def L7 : Level := mkLevel 7 R6
def L8 : Level := mkLevel 8 R7

def combos8 : List (Nat × Nat × Nat × Nat) := combos 8

/-- Number of leaves below the first-stage choices `lo ≤ i < hi` (testing). -/
def countRange (lo hi : Nat) : Nat :=
  (((cands (L8.stages.getD 0 ⟨#[], #[], #[]⟩) []).drop lo).take (hi - lo)).map (fun T =>
    Task.spawn fun _ => (go L8 (fun _ => true) (L8.n - 1) [T]).length)
    |>.foldl (fun a t => a + t.get) 0

end Fast
