import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_80 : Data.endpointOk Data.patterns[80]! = true := by decide +kernel

theorem endpoints_81 : Data.endpointOk Data.patterns[81]! = true := by decide +kernel

theorem endpoints_82 : Data.endpointOk Data.patterns[82]! = true := by decide +kernel

theorem endpoints_83 : Data.endpointOk Data.patterns[83]! = true := by decide +kernel

end Fast.Five.Checked
