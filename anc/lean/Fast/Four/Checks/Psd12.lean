import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd1_8 : psdRow Data.low Data.high Data.block1 8 = true := by decide +kernel

theorem psd1_9 : psdRow Data.low Data.high Data.block1 9 = true := by decide +kernel

theorem psd1_10 : psdRow Data.low Data.high Data.block1 10 = true := by decide +kernel

theorem psd1_11 : psdRow Data.low Data.high Data.block1 11 = true := by decide +kernel

end Fast.Four.Checked
