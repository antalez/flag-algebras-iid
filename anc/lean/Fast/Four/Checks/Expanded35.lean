import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem expanded3_20 : expandedRow Data.block3 20 = true := by decide +kernel

end Fast.Four.Checked
