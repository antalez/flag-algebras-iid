import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_216 : Data.endpointOk Data.patterns[216]! = true := by decide +kernel

end Fast.Four.Checked
