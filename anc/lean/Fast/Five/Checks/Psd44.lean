import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd4_16 : psdRow Data.low Data.high Data.block4 16 = true := by decide +kernel

theorem psd4_17 : psdRow Data.low Data.high Data.block4 17 = true := by decide +kernel

end Fast.Five.Checked
