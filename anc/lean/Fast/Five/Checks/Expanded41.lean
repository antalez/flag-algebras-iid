import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem expanded4_4 : expandedRow Data.block4 4 = true := by decide +kernel

theorem expanded4_5 : expandedRow Data.block4 5 = true := by decide +kernel

theorem expanded4_6 : expandedRow Data.block4 6 = true := by decide +kernel

theorem expanded4_7 : expandedRow Data.block4 7 = true := by decide +kernel

end Fast.Five.Checked
