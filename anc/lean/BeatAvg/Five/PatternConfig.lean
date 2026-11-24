import BeatAvg.Five.BitSpecs
import BeatAvg.Five.Config
import BeatAvg.Cert.SortedN

namespace BeatAvg.Five
open Fast.Five

theorem quadIndex_ok : IdxOk 5 quadIndex := by
  intro w a b c d hab hbc hcd hd
  have ha : a < 5 := by omega
  have hb : b < 5 := by omega
  have hc : c < 5 := by omega
  interval_cases a <;> interval_cases b <;> try omega
  all_goals interval_cases c <;> interval_cases d <;> try omega
  all_goals norm_num [quadIndex, quads, choose, patArr, Fast.combos, List.range_succ, List.filterMap]

theorem additiveTrits_eq {p : Pattern} {v : Fin 5 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    additiveTrits p = patArr 5 (extNn v) := by
  norm_num [additiveTrits, wins, win, quads, choose, patArr, Fast.combos, List.range_succ,
    trit, extNn]
  rw [bit10_spec hb, bit11_spec hb, bit12_spec hb, bit13_spec hb, bit14_spec hb, bit15_spec hb, bit16_spec hb, bit17_spec hb, bit18_spec hb, bit19_spec hb]
  simp [trit, extNn, Nat.add_comm]

/-- The real colored configuration of a sorted sample is exactly the one
reconstructed from its certified bits. The additive part reuses `cfgOf_eq_patG`. -/
theorem configOf_eq_pattern {p : Pattern} {v : Fin 5 → ℝ}
    (hv : Generic v) (hm : Monotone v)
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    configOf v = patternConfig p := by
  have hs : SGn 5 v := ⟨hm.strictMono_of_injective hv.2.1, hv.1, hv.2.2.1⟩
  change Fast.Five.Config.mk _ _ = Fast.Five.Config.mk _ _
  rw [Fast.Five.Config.mk.injEq]
  constructor
  · rw [additiveTrits_eq hb]
    exact cfgOf_eq_patG (by decide) quadIndex_ok hs
  · funext i j
    have h01 := hm (show (0 : Fin 5) ≤ 1 by decide)
    have h02 := hm (show (0 : Fin 5) ≤ 2 by decide)
    have h03 := hm (show (0 : Fin 5) ≤ 3 by decide)
    have h04 := hm (show (0 : Fin 5) ≤ 4 by decide)
    have h12 := hm (show (1 : Fin 5) ≤ 2 by decide)
    have h13 := hm (show (1 : Fin 5) ≤ 3 by decide)
    have h14 := hm (show (1 : Fin 5) ≤ 4 by decide)
    have h23 := hm (show (2 : Fin 5) ≤ 3 by decide)
    have h24 := hm (show (2 : Fin 5) ≤ 4 by decide)
    have h34 := hm (show (3 : Fin 5) ≤ 4 by decide)
    fin_cases i <;> fin_cases j <;> norm_num [edge, pairs, List.range_succ,
      min_eq_left h01, min_eq_right h01, max_eq_left h01, max_eq_right h01,
      min_eq_left h02, min_eq_right h02, max_eq_left h02, max_eq_right h02,
      min_eq_left h03, min_eq_right h03, max_eq_left h03, max_eq_right h03,
      min_eq_left h04, min_eq_right h04, max_eq_left h04, max_eq_right h04,
      min_eq_left h12, min_eq_right h12, max_eq_left h12, max_eq_right h12,
      min_eq_left h13, min_eq_right h13, max_eq_left h13, max_eq_right h13,
      min_eq_left h14, min_eq_right h14, max_eq_left h14, max_eq_right h14,
      min_eq_left h23, min_eq_right h23, max_eq_left h23, max_eq_right h23,
      min_eq_left h24, min_eq_right h24, max_eq_left h24, max_eq_right h24,
      min_eq_left h34, min_eq_right h34, max_eq_left h34, max_eq_right h34,
      bit0_spec hb, bit1_spec hb, bit2_spec hb, bit3_spec hb, bit4_spec hb, bit5_spec hb, bit6_spec hb, bit7_spec hb, bit8_spec hb, bit9_spec hb]

end BeatAvg.Five
