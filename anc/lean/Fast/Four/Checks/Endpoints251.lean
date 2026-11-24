import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_251 : Data.endpointOk Data.patterns[251]! = true := by decide +kernel

end Fast.Four.Checked
