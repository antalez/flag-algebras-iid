import Fast.Four.Basic

namespace Fast.Four

def objectiveCount (t : Nat) : Nat :=
  (all4.map fun l =>
    bitNat ((cfgOfPatG 4 quadIndex #[t]).sb (fn4 l 0) (fn4 l 1) (fn4 l 2) (fn4 l 3))).sum

/-- Six permutations for each winning target; three possible trits. -/
theorem objectiveCount_ok : ∀ t : Fin 3, objectiveCount t.val = 6*t.val := by
  decide +kernel

end Fast.Four
