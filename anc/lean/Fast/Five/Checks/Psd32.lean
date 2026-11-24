import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd3_8 : psdRow Data.low Data.high Data.block3 8 = true := by decide +kernel

theorem psd3_9 : psdRow Data.low Data.high Data.block3 9 = true := by decide +kernel

theorem psd3_10 : psdRow Data.low Data.high Data.block3 10 = true := by decide +kernel

theorem psd3_11 : psdRow Data.low Data.high Data.block3 11 = true := by decide +kernel

end Fast.Five.Checked
