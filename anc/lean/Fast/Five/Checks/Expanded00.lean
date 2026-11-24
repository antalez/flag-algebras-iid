import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded0_0 : expandedRow Data.block0 0 = true := by decide +kernel

theorem expanded0_1 : expandedRow Data.block0 1 = true := by decide +kernel

theorem expanded0_2 : expandedRow Data.block0 2 = true := by decide +kernel

theorem expanded0_3 : expandedRow Data.block0 3 = true := by decide +kernel

end Fast.Five.Checked
