import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_296 : Data.endpointOk Data.patterns[296]! = true := by decide +kernel

theorem endpoints_297 : Data.endpointOk Data.patterns[297]! = true := by decide +kernel

theorem endpoints_298 : Data.endpointOk Data.patterns[298]! = true := by decide +kernel

theorem endpoints_299 : Data.endpointOk Data.patterns[299]! = true := by decide +kernel

end Fast.Five.Checked
