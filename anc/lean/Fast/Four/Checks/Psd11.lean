import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd1_4 : psdRow Data.low Data.high Data.block1 4 = true := by decide +kernel

theorem psd1_5 : psdRow Data.low Data.high Data.block1 5 = true := by decide +kernel

theorem psd1_6 : psdRow Data.low Data.high Data.block1 6 = true := by decide +kernel

theorem psd1_7 : psdRow Data.low Data.high Data.block1 7 = true := by decide +kernel

end Fast.Four.Checked
