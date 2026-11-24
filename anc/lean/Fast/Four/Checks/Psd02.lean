import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd0_8 : psdRow Data.low Data.high Data.block0 8 = true := by decide +kernel

end Fast.Four.Checked
