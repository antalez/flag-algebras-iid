import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded1_8 : expandedRow Data.block1 8 = true := by decide +kernel

theorem expanded1_9 : expandedRow Data.block1 9 = true := by decide +kernel

theorem expanded1_10 : expandedRow Data.block1 10 = true := by decide +kernel

theorem expanded1_11 : expandedRow Data.block1 11 = true := by decide +kernel

end Fast.Five.Checked
