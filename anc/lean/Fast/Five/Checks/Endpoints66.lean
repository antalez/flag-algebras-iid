import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_264 : Data.endpointOk Data.patterns[264]! = true := by decide +kernel

theorem endpoints_265 : Data.endpointOk Data.patterns[265]! = true := by decide +kernel

theorem endpoints_266 : Data.endpointOk Data.patterns[266]! = true := by decide +kernel

theorem endpoints_267 : Data.endpointOk Data.patterns[267]! = true := by decide +kernel

end Fast.Five.Checked
