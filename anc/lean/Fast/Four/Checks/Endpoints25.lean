import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_25 : Data.endpointOk Data.patterns[25]! = true := by decide +kernel

end Fast.Four.Checked
