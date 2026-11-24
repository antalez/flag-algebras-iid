import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd0_4 : psdRow Data.low Data.high Data.block0 4 = true := by decide +kernel

theorem psd0_5 : psdRow Data.low Data.high Data.block0 5 = true := by decide +kernel

theorem psd0_6 : psdRow Data.low Data.high Data.block0 6 = true := by decide +kernel

theorem psd0_7 : psdRow Data.low Data.high Data.block0 7 = true := by decide +kernel

end Fast.Four.Checked
