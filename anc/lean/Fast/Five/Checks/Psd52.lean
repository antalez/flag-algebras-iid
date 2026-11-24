import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd5_8 : psdRow Data.low Data.high Data.block5 8 = true := by decide +kernel

theorem psd5_9 : psdRow Data.low Data.high Data.block5 9 = true := by decide +kernel

theorem psd5_10 : psdRow Data.low Data.high Data.block5 10 = true := by decide +kernel

theorem psd5_11 : psdRow Data.low Data.high Data.block5 11 = true := by decide +kernel

end Fast.Five.Checked
