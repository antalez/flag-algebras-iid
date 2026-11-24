import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd1_0 : psdRow Data.low Data.high Data.block1 0 = true := by decide +kernel

theorem psd1_1 : psdRow Data.low Data.high Data.block1 1 = true := by decide +kernel

theorem psd1_2 : psdRow Data.low Data.high Data.block1 2 = true := by decide +kernel

theorem psd1_3 : psdRow Data.low Data.high Data.block1 3 = true := by decide +kernel

end Fast.Four.Checked
