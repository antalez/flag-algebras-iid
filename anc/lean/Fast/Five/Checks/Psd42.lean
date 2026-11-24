import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd4_8 : psdRow Data.low Data.high Data.block4 8 = true := by decide +kernel

theorem psd4_9 : psdRow Data.low Data.high Data.block4 9 = true := by decide +kernel

theorem psd4_10 : psdRow Data.low Data.high Data.block4 10 = true := by decide +kernel

theorem psd4_11 : psdRow Data.low Data.high Data.block4 11 = true := by decide +kernel

end Fast.Five.Checked
