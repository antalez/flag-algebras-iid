import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd2_0 : psdRow Data.low Data.high Data.block2 0 = true := by decide +kernel

theorem psd2_1 : psdRow Data.low Data.high Data.block2 1 = true := by decide +kernel

theorem psd2_2 : psdRow Data.low Data.high Data.block2 2 = true := by decide +kernel

theorem psd2_3 : psdRow Data.low Data.high Data.block2 3 = true := by decide +kernel

end Fast.Four.Checked
