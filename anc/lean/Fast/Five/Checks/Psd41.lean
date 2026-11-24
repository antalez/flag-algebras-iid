import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd4_4 : psdRow Data.low Data.high Data.block4 4 = true := by decide +kernel

theorem psd4_5 : psdRow Data.low Data.high Data.block4 5 = true := by decide +kernel

theorem psd4_6 : psdRow Data.low Data.high Data.block4 6 = true := by decide +kernel

theorem psd4_7 : psdRow Data.low Data.high Data.block4 7 = true := by decide +kernel

end Fast.Five.Checked
