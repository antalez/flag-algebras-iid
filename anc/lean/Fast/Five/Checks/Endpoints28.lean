import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_112 : Data.endpointOk Data.patterns[112]! = true := by decide +kernel

theorem endpoints_113 : Data.endpointOk Data.patterns[113]! = true := by decide +kernel

theorem endpoints_114 : Data.endpointOk Data.patterns[114]! = true := by decide +kernel

theorem endpoints_115 : Data.endpointOk Data.patterns[115]! = true := by decide +kernel

end Fast.Five.Checked
