import Fast.Four.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Four.Checked

theorem endpoints_153 : Data.endpointOk Data.patterns[153]! = true := by decide +kernel

end Fast.Four.Checked
