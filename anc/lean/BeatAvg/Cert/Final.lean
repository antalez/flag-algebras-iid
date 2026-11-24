import BeatAvg.Cert.Main8
import BeatAvg.Cert.BstarFacts
import BeatAvg.Lower.Main

/-!
# `C = B*`

`C = sup_μ P(X₁ + X₂ + X₃ < 2 X₄)` over laws `μ` on `[0, ∞)`, and
`B* = (r³ - 6r² + 6r)/4 = r(2 - r)/(1 + r + r² + r³)` with `r` the root of
`x⁴ - 4x³ - 3x² - 2x + 2` in `[0, 1]`.

The upper bound is the order-8 certificate (`Main8`) through Theorem D and the two-point criterion
(`BeatAvg.Main`), with the trivial bound `C ≤ 1` as second point: no flag bound of lower order is
used. The finite check of the certificate is performed by `native_decide`.

The lower bound `B* ≤ C` (`BeatAvg.Lower.Main`) is the construction of Bellec and Fritz; it uses no
computation.
-/

namespace BeatAvg

/-- **The Beat the Average constant is at most `B*`.** -/
theorem C_le_Bstar : C ≤ Bstar := C_le_Bstar_of_main8

/-- **The Beat the Average constant equals `B*`.** The upper bound depends on one finite check run by
`native_decide`; the lower bound does not. -/
theorem C_eq_Bstar : C = Bstar := le_antisymm C_le_Bstar Bstar_le_C

/-- Numerically, `C < 0.40069538`. -/
theorem C_lt : C < 40069538 / 100000000 := lt_of_le_of_lt C_le_Bstar Bstar_bounds.2

end BeatAvg
