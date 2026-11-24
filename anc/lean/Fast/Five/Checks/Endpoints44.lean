import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_176 : Data.endpointOk Data.patterns[176]! = true := by decide +kernel

theorem endpoints_177 : Data.endpointOk Data.patterns[177]! = true := by decide +kernel

theorem endpoints_178 : Data.endpointOk Data.patterns[178]! = true := by decide +kernel

theorem endpoints_179 : Data.endpointOk Data.patterns[179]! = true := by decide +kernel

end Fast.Five.Checked
