import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_292 : Data.endpointOk Data.patterns[292]! = true := by decide +kernel

theorem endpoints_293 : Data.endpointOk Data.patterns[293]! = true := by decide +kernel

theorem endpoints_294 : Data.endpointOk Data.patterns[294]! = true := by decide +kernel

theorem endpoints_295 : Data.endpointOk Data.patterns[295]! = true := by decide +kernel

end Fast.Five.Checked
