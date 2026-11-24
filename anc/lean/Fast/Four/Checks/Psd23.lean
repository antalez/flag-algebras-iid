import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd2_12 : psdRow Data.low Data.high Data.block2 12 = true := by decide +kernel

theorem psd2_13 : psdRow Data.low Data.high Data.block2 13 = true := by decide +kernel

end Fast.Four.Checked
