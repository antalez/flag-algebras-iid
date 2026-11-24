import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd3_12 : psdRow Data.low Data.high Data.block3 12 = true := by decide +kernel

theorem psd3_13 : psdRow Data.low Data.high Data.block3 13 = true := by decide +kernel

theorem psd3_14 : psdRow Data.low Data.high Data.block3 14 = true := by decide +kernel

theorem psd3_15 : psdRow Data.low Data.high Data.block3 15 = true := by decide +kernel

end Fast.Five.Checked
