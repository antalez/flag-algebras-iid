import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_236 : Data.endpointOk Data.patterns[236]! = true := by decide +kernel

theorem endpoints_237 : Data.endpointOk Data.patterns[237]! = true := by decide +kernel

theorem endpoints_238 : Data.endpointOk Data.patterns[238]! = true := by decide +kernel

theorem endpoints_239 : Data.endpointOk Data.patterns[239]! = true := by decide +kernel

end Fast.Five.Checked
