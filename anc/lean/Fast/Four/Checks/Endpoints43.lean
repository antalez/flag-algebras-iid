import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_43 : Data.endpointOk Data.patterns[43]! = true := by decide +kernel

end Fast.Four.Checked
