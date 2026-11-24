import BeatAvg.Six.Sound
import BeatAvg.Six.Cover
import BeatAvg.Six.Checks

/-!
# The six-point flag bound `C ≤ 0.40255`

`C ≤ 201272564718335614989 / 500000000000000000000 = 0.402545129...`, from the six-point flag
certificate of `starting_point/cert_6_json.txt`. No `native_decide`: the search for the patterns
of six points and the evaluation of the certificate on the 1,290 patterns are run by the kernel.
This file is independent of the proof of `C = B*`.
-/

namespace BeatAvg

/-- **The six-point flag bound.** -/
theorem C_le_six : C ≤ 201272564718335614989 / 500000000000000000000 := by
  have h := Six.C_le_of_checks (fun w hw => Six.cover6 hw)
    (fun v hv => List.all_eq_true.1 Six.all_checks v hv)
  have e : ((Six.D.lamP : ℤ) : ℝ) / ((Six.D.lamQ : ℤ) : ℝ)
      = 201272564718335614989 / 500000000000000000000 := by
    simp [Six.D.lamP, Six.D.lamQ]
  rwa [e] at h

/-- `C ≤ 0.40255`. -/
theorem C_le_40255 : C ≤ 40255 / 100000 := C_le_six.trans (by norm_num)

end BeatAvg
