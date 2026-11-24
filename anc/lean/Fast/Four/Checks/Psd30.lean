import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd3_0 : psdRow Data.low Data.high Data.block3 0 = true := by decide +kernel

theorem psd3_1 : psdRow Data.low Data.high Data.block3 1 = true := by decide +kernel

theorem psd3_2 : psdRow Data.low Data.high Data.block3 2 = true := by decide +kernel

theorem psd3_3 : psdRow Data.low Data.high Data.block3 3 = true := by decide +kernel

end Fast.Four.Checked
