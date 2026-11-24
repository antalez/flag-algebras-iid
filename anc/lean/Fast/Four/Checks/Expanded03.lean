import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded0_12 : expandedRow Data.block0 12 = true := by decide +kernel

theorem expanded0_13 : expandedRow Data.block0 13 = true := by decide +kernel

theorem expanded0_14 : expandedRow Data.block0 14 = true := by decide +kernel

end Fast.Four.Checked
