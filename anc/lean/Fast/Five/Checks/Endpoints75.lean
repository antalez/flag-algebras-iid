import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_300 : Data.endpointOk Data.patterns[300]! = true := by decide +kernel

theorem endpoints_301 : Data.endpointOk Data.patterns[301]! = true := by decide +kernel

theorem endpoints_302 : Data.endpointOk Data.patterns[302]! = true := by decide +kernel

theorem endpoints_303 : Data.endpointOk Data.patterns[303]! = true := by decide +kernel

end Fast.Five.Checked
