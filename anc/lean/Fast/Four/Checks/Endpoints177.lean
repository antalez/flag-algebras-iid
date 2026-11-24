import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_177 : Data.endpointOk Data.patterns[177]! = true := by decide +kernel

end Fast.Four.Checked
