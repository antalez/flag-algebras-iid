import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd1_4 : psdRow Data.low Data.high Data.block1 4 = true := by decide +kernel

end Fast.Five.Checked
