import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd2_4 : psdRow Data.low Data.high Data.block2 4 = true := by decide +kernel

theorem psd2_5 : psdRow Data.low Data.high Data.block2 5 = true := by decide +kernel

theorem psd2_6 : psdRow Data.low Data.high Data.block2 6 = true := by decide +kernel

theorem psd2_7 : psdRow Data.low Data.high Data.block2 7 = true := by decide +kernel

end Fast.Four.Checked
