import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_76 : Data.endpointOk Data.patterns[76]! = true := by decide +kernel

theorem endpoints_77 : Data.endpointOk Data.patterns[77]! = true := by decide +kernel

theorem endpoints_78 : Data.endpointOk Data.patterns[78]! = true := by decide +kernel

theorem endpoints_79 : Data.endpointOk Data.patterns[79]! = true := by decide +kernel

end Fast.Five.Checked
