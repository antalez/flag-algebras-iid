import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_140 : Data.endpointOk Data.patterns[140]! = true := by decide +kernel

theorem endpoints_141 : Data.endpointOk Data.patterns[141]! = true := by decide +kernel

theorem endpoints_142 : Data.endpointOk Data.patterns[142]! = true := by decide +kernel

theorem endpoints_143 : Data.endpointOk Data.patterns[143]! = true := by decide +kernel

end Fast.Five.Checked
