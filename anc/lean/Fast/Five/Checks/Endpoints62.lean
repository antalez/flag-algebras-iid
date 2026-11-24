import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_248 : Data.endpointOk Data.patterns[248]! = true := by decide +kernel

theorem endpoints_249 : Data.endpointOk Data.patterns[249]! = true := by decide +kernel

theorem endpoints_250 : Data.endpointOk Data.patterns[250]! = true := by decide +kernel

theorem endpoints_251 : Data.endpointOk Data.patterns[251]! = true := by decide +kernel

end Fast.Five.Checked
