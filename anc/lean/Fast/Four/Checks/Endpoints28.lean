import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_28 : Data.endpointOk Data.patterns[28]! = true := by decide +kernel

end Fast.Four.Checked
