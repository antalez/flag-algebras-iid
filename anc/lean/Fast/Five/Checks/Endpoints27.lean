import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_108 : Data.endpointOk Data.patterns[108]! = true := by decide +kernel

theorem endpoints_109 : Data.endpointOk Data.patterns[109]! = true := by decide +kernel

theorem endpoints_110 : Data.endpointOk Data.patterns[110]! = true := by decide +kernel

theorem endpoints_111 : Data.endpointOk Data.patterns[111]! = true := by decide +kernel

end Fast.Five.Checked
