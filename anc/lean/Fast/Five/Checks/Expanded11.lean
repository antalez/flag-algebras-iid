import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded1_4 : expandedRow Data.block1 4 = true := by decide +kernel

theorem expanded1_5 : expandedRow Data.block1 5 = true := by decide +kernel

theorem expanded1_6 : expandedRow Data.block1 6 = true := by decide +kernel

theorem expanded1_7 : expandedRow Data.block1 7 = true := by decide +kernel

end Fast.Five.Checked
