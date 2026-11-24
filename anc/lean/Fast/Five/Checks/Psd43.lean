import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd4_12 : psdRow Data.low Data.high Data.block4 12 = true := by decide +kernel

theorem psd4_13 : psdRow Data.low Data.high Data.block4 13 = true := by decide +kernel

theorem psd4_14 : psdRow Data.low Data.high Data.block4 14 = true := by decide +kernel

theorem psd4_15 : psdRow Data.low Data.high Data.block4 15 = true := by decide +kernel

end Fast.Five.Checked
