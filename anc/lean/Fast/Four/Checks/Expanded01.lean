import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded0_4 : expandedRow Data.block0 4 = true := by decide +kernel

theorem expanded0_5 : expandedRow Data.block0 5 = true := by decide +kernel

theorem expanded0_6 : expandedRow Data.block0 6 = true := by decide +kernel

theorem expanded0_7 : expandedRow Data.block0 7 = true := by decide +kernel

end Fast.Four.Checked
