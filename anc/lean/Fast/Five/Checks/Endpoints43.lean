import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_172 : Data.endpointOk Data.patterns[172]! = true := by decide +kernel

theorem endpoints_173 : Data.endpointOk Data.patterns[173]! = true := by decide +kernel

theorem endpoints_174 : Data.endpointOk Data.patterns[174]! = true := by decide +kernel

theorem endpoints_175 : Data.endpointOk Data.patterns[175]! = true := by decide +kernel

end Fast.Five.Checked
