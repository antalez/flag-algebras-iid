import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_288 : Data.endpointOk Data.patterns[288]! = true := by decide +kernel

theorem endpoints_289 : Data.endpointOk Data.patterns[289]! = true := by decide +kernel

theorem endpoints_290 : Data.endpointOk Data.patterns[290]! = true := by decide +kernel

theorem endpoints_291 : Data.endpointOk Data.patterns[291]! = true := by decide +kernel

end Fast.Five.Checked
