import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_42 : Data.endpointOk Data.patterns[42]! = true := by decide +kernel

end Fast.Four.Checked
