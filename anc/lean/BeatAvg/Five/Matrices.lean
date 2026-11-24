import BeatAvg.Five.Matrix

import Fast.Five.Checked

namespace BeatAvg.Five

open Fast.Five

theorem block0_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block0 a.val b.val) * v b :=
  block_psd enclosure_real Data.block0 Checked.shape0 Checked.psd0 v

theorem block1_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block1 a.val b.val) * v b :=
  block_psd enclosure_real Data.block1 Checked.shape1 Checked.psd1 v

theorem block2_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block2 a.val b.val) * v b :=
  block_psd enclosure_real Data.block2 Checked.shape2 Checked.psd2 v

theorem block3_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block3 a.val b.val) * v b :=
  block_psd enclosure_real Data.block3 Checked.shape3 Checked.psd3 v

theorem block4_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block4 a.val b.val) * v b :=
  block_psd enclosure_real Data.block4 Checked.shape4 Checked.psd4 v

theorem block5_psd {M : ℕ} (v : Fin M → ℝ) :
    0 ≤ ∑ a, ∑ b, v a * evalK (expandedEntry Data.block5 a.val b.val) * v b :=
  block_psd enclosure_real Data.block5 Checked.shape5 Checked.psd5 v

end BeatAvg.Five
