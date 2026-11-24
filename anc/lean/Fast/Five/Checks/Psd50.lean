import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd5_0 : psdRow Data.low Data.high Data.block5 0 = true := by decide +kernel

theorem psd5_1 : psdRow Data.low Data.high Data.block5 1 = true := by decide +kernel

theorem psd5_2 : psdRow Data.low Data.high Data.block5 2 = true := by decide +kernel

theorem psd5_3 : psdRow Data.low Data.high Data.block5 3 = true := by decide +kernel

end Fast.Five.Checked
