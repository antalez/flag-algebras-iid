import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd0_4 : psdRow Data.low Data.high Data.block0 4 = true := by decide +kernel

theorem psd0_5 : psdRow Data.low Data.high Data.block0 5 = true := by decide +kernel

theorem psd0_6 : psdRow Data.low Data.high Data.block0 6 = true := by decide +kernel

end Fast.Five.Checked
