import BeatAvg.Four.BitSpecs
import BeatAvg.Cert.SortedN

namespace BeatAvg.Four
open Fast.Four
set_option maxHeartbeats 0

theorem quadIndex_ok : IdxOk 4 quadIndex := by
  intro w a b c d hab hbc hcd hd
  have ha : a = 0 := by omega
  have hb : b = 1 := by omega
  have hc : c = 2 := by omega
  have he : d = 3 := by omega
  subst a; subst b; subst c; subst d
  norm_num [quadIndex, patArr, Fast.combos, List.range_succ, List.filterMap]

theorem additiveTrits_eq {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    additiveTrits p = patArr 4 (extNn v) := by
  norm_num [additiveTrits, wins, patArr, Fast.combos, List.range_succ, trit, extNn]
  rw [bit18_spec hb, bit19_spec hb]
  simp [trit, extNn, Nat.add_comm]

theorem configOf_eq_pattern {p : Pattern} {v : Fin 4 → ℝ}
    (hv : Generic v) (hm : Monotone v)
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    configOf v = patternConfig p := by
  have hs : SGn 4 v := ⟨hm.strictMono_of_injective hv.1.2.1, hv.1.1, hv.1.2.2⟩
  change Fast.Four.Config.mk _ _ = Fast.Four.Config.mk _ _
  rw [Fast.Four.Config.mk.injEq]
  constructor
  · rw [additiveTrits_eq hb]
    exact cfgOf_eq_patG (by decide) quadIndex_ok hs
  · funext q i j
    have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
    have h02 := hm (show (0 : Fin 4) ≤ 2 by decide)
    have h03 := hm (show (0 : Fin 4) ≤ 3 by decide)
    have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
    have h13 := hm (show (1 : Fin 4) ≤ 3 by decide)
    have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
    fin_cases q <;> fin_cases i <;> fin_cases j <;> norm_num [edge, pairs, Fast.Five.pairs, List.range_succ,
      min_eq_left h01, min_eq_right h01, max_eq_left h01, max_eq_right h01,
      min_eq_left h02, min_eq_right h02, max_eq_left h02, max_eq_right h02,
      min_eq_left h03, min_eq_right h03, max_eq_left h03, max_eq_right h03,
      min_eq_left h12, min_eq_right h12, max_eq_left h12, max_eq_right h12,
      min_eq_left h13, min_eq_right h13, max_eq_left h13, max_eq_right h13,
      min_eq_left h23, min_eq_right h23, max_eq_left h23, max_eq_right h23,
      bit0_spec hb, bit1_spec hb, bit2_spec hb, bit3_spec hb,
      bit4_spec hb, bit5_spec hb, bit6_spec hb, bit7_spec hb,
      bit8_spec hb, bit9_spec hb, bit10_spec hb, bit11_spec hb,
      bit12_spec hb, bit13_spec hb, bit14_spec hb, bit15_spec hb,
      bit16_spec hb, bit17_spec hb]

end BeatAvg.Four
