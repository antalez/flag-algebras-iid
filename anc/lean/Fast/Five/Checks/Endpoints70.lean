import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_280 : Data.endpointOk Data.patterns[280]! = true := by decide +kernel

theorem endpoints_281 : Data.endpointOk Data.patterns[281]! = true := by decide +kernel

theorem endpoints_282 : Data.endpointOk Data.patterns[282]! = true := by decide +kernel

theorem endpoints_283 : Data.endpointOk Data.patterns[283]! = true := by decide +kernel

end Fast.Five.Checked
