import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_116 : Data.endpointOk Data.patterns[116]! = true := by decide +kernel

theorem endpoints_117 : Data.endpointOk Data.patterns[117]! = true := by decide +kernel

theorem endpoints_118 : Data.endpointOk Data.patterns[118]! = true := by decide +kernel

theorem endpoints_119 : Data.endpointOk Data.patterns[119]! = true := by decide +kernel

end Fast.Five.Checked
