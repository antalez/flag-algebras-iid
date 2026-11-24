import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd3_16 : psdRow Data.low Data.high Data.block3 16 = true := by decide +kernel

theorem psd3_17 : psdRow Data.low Data.high Data.block3 17 = true := by decide +kernel

theorem psd3_18 : psdRow Data.low Data.high Data.block3 18 = true := by decide +kernel

theorem psd3_19 : psdRow Data.low Data.high Data.block3 19 = true := by decide +kernel

end Fast.Five.Checked
