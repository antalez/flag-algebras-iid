import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_272 : Data.endpointOk Data.patterns[272]! = true := by decide +kernel

theorem endpoints_273 : Data.endpointOk Data.patterns[273]! = true := by decide +kernel

theorem endpoints_274 : Data.endpointOk Data.patterns[274]! = true := by decide +kernel

theorem endpoints_275 : Data.endpointOk Data.patterns[275]! = true := by decide +kernel

end Fast.Five.Checked
