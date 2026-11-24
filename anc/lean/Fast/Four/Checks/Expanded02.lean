import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded0_8 : expandedRow Data.block0 8 = true := by decide +kernel

theorem expanded0_9 : expandedRow Data.block0 9 = true := by decide +kernel

theorem expanded0_10 : expandedRow Data.block0 10 = true := by decide +kernel

theorem expanded0_11 : expandedRow Data.block0 11 = true := by decide +kernel

end Fast.Four.Checked
