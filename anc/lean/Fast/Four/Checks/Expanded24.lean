import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded2_16 : expandedRow Data.block2 16 = true := by decide +kernel

theorem expanded2_17 : expandedRow Data.block2 17 = true := by decide +kernel

theorem expanded2_18 : expandedRow Data.block2 18 = true := by decide +kernel

end Fast.Four.Checked
