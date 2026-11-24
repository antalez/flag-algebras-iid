import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd4_0 : psdRow Data.low Data.high Data.block4 0 = true := by decide +kernel

theorem psd4_1 : psdRow Data.low Data.high Data.block4 1 = true := by decide +kernel

theorem psd4_2 : psdRow Data.low Data.high Data.block4 2 = true := by decide +kernel

theorem psd4_3 : psdRow Data.low Data.high Data.block4 3 = true := by decide +kernel

end Fast.Five.Checked
