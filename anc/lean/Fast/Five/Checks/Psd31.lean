import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd3_4 : psdRow Data.low Data.high Data.block3 4 = true := by decide +kernel

theorem psd3_5 : psdRow Data.low Data.high Data.block3 5 = true := by decide +kernel

theorem psd3_6 : psdRow Data.low Data.high Data.block3 6 = true := by decide +kernel

theorem psd3_7 : psdRow Data.low Data.high Data.block3 7 = true := by decide +kernel

end Fast.Five.Checked
