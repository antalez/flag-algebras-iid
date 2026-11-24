import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_256 : Data.endpointOk Data.patterns[256]! = true := by decide +kernel

theorem endpoints_257 : Data.endpointOk Data.patterns[257]! = true := by decide +kernel

theorem endpoints_258 : Data.endpointOk Data.patterns[258]! = true := by decide +kernel

theorem endpoints_259 : Data.endpointOk Data.patterns[259]! = true := by decide +kernel

end Fast.Five.Checked
