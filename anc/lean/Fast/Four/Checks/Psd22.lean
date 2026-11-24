import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd2_8 : psdRow Data.low Data.high Data.block2 8 = true := by decide +kernel

theorem psd2_9 : psdRow Data.low Data.high Data.block2 9 = true := by decide +kernel

theorem psd2_10 : psdRow Data.low Data.high Data.block2 10 = true := by decide +kernel

theorem psd2_11 : psdRow Data.low Data.high Data.block2 11 = true := by decide +kernel

end Fast.Four.Checked
