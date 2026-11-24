import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd2_4 : psdRow Data.low Data.high Data.block2 4 = true := by decide +kernel

theorem psd2_5 : psdRow Data.low Data.high Data.block2 5 = true := by decide +kernel

end Fast.Five.Checked
