import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_254 : Data.endpointOk Data.patterns[254]! = true := by decide +kernel

end Fast.Four.Checked
