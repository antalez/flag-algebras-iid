import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_276 : Data.endpointOk Data.patterns[276]! = true := by decide +kernel

theorem endpoints_277 : Data.endpointOk Data.patterns[277]! = true := by decide +kernel

theorem endpoints_278 : Data.endpointOk Data.patterns[278]! = true := by decide +kernel

theorem endpoints_279 : Data.endpointOk Data.patterns[279]! = true := by decide +kernel

end Fast.Five.Checked
