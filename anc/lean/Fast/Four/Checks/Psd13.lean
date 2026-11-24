import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem psd1_12 : psdRow Data.low Data.high Data.block1 12 = true := by decide +kernel

end Fast.Four.Checked
