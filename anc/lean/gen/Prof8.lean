import BeatAvg.K8.Check8K

/-!
Profile of the join of every pattern of seven points, used by `gen/gen_k8.py` to cut the order-8
check into pieces. For each pattern `(g, j)` and each candidate of the first stage of its join: the
number of leaves and the number of compatibility tests of the plain join (a measure of the work).
`gen/run_prof.sh` runs this file on 144 ranges of groups in separate processes (threads sharing the
data are much slower) and writes `data/k8_profile.txt`.
-/

open BeatAvg.K8

/-- states after the stages, counting the compatibility tests -/
def runStages (T : Nat) : Nat → Nat → Nat → List Nat → Nat → List Nat × Nat
  | 0, _, _, st, tests => (st, tests)
  | f + 1, j, A, st, tests =>
    let E := candsJ D.G7 40 7 T j
    let st' := extAll (Nat.land A (maskM (avoidT 7 j))) E st
    runStages T f (j + 1) (Nat.lor A (maskM (avoidT 7 j))) st' (tests + st.length * E.length)

/-- for each first-stage candidate: (leaves, tests) -/
def profile (T : Nat) : List (Nat × Nat) :=
  (candsJ D.G7 40 7 T 0).map fun c =>
    let r := runStages T 6 1 (maskM (avoidT 7 0)) [c] 0
    (r.1.length, r.2)

def part (lo hi : Nat) : IO Unit := do
  let mut out := ""
  for g in List.range' lo (hi - lo) do
    let grp := nth (0, 0, 0) D.G7 g
    for j in List.range grp.2.1 do
      let pr := profile (T7 g j)
      out := out ++ s!"{g} {j} " ++ " ".intercalate (pr.map fun p => s!"{p.1}:{p.2}") ++ "\n"
  IO.FS.writeFile s!"scratch/prof/p{lo}.txt" out

#eval part LO HI

