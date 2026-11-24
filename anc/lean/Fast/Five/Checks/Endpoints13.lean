import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_52 : Data.endpointOk Data.patterns[52]! = true := by decide +kernel

theorem endpoints_53 : Data.endpointOk Data.patterns[53]! = true := by decide +kernel

theorem endpoints_54 : Data.endpointOk Data.patterns[54]! = true := by decide +kernel

theorem endpoints_55 : Data.endpointOk Data.patterns[55]! = true := by decide +kernel

end Fast.Five.Checked
