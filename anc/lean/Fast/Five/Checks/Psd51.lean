import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd5_4 : psdRow Data.low Data.high Data.block5 4 = true := by decide +kernel

theorem psd5_5 : psdRow Data.low Data.high Data.block5 5 = true := by decide +kernel

theorem psd5_6 : psdRow Data.low Data.high Data.block5 6 = true := by decide +kernel

theorem psd5_7 : psdRow Data.low Data.high Data.block5 7 = true := by decide +kernel

end Fast.Five.Checked
