import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_144 : Data.endpointOk Data.patterns[144]! = true := by decide +kernel

theorem endpoints_145 : Data.endpointOk Data.patterns[145]! = true := by decide +kernel

theorem endpoints_146 : Data.endpointOk Data.patterns[146]! = true := by decide +kernel

theorem endpoints_147 : Data.endpointOk Data.patterns[147]! = true := by decide +kernel

end Fast.Five.Checked
