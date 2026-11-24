import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd5_12 : psdRow Data.low Data.high Data.block5 12 = true := by decide +kernel

theorem psd5_13 : psdRow Data.low Data.high Data.block5 13 = true := by decide +kernel

theorem psd5_14 : psdRow Data.low Data.high Data.block5 14 = true := by decide +kernel

end Fast.Five.Checked
