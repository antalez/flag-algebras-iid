import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_260 : Data.endpointOk Data.patterns[260]! = true := by decide +kernel

theorem endpoints_261 : Data.endpointOk Data.patterns[261]! = true := by decide +kernel

theorem endpoints_262 : Data.endpointOk Data.patterns[262]! = true := by decide +kernel

theorem endpoints_263 : Data.endpointOk Data.patterns[263]! = true := by decide +kernel

end Fast.Five.Checked
