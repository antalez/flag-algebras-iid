import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem cover : coverOk Data.patterns Data.cover 0 0 = true := by decide +kernel

end Fast.Four.Checked
