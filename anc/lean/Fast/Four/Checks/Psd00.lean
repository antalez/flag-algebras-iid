import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd0_0 : psdRow Data.low Data.high Data.block0 0 = true := by decide +kernel

theorem psd0_1 : psdRow Data.low Data.high Data.block0 1 = true := by decide +kernel

theorem psd0_2 : psdRow Data.low Data.high Data.block0 2 = true := by decide +kernel

theorem psd0_3 : psdRow Data.low Data.high Data.block0 3 = true := by decide +kernel

end Fast.Four.Checked
