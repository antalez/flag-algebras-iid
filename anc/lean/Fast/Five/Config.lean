import Fast.Pat

namespace Fast.Five
/-- Order, additive comparisons, and the loopless symmetric pair color. -/
structure Config (n : Nat) where
  additive : Fast.Cfg n
  close : Fin n → Fin n → Bool
end Fast.Five
