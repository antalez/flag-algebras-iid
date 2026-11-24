import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_128 : Data.endpointOk Data.patterns[128]! = true := by decide +kernel

theorem endpoints_129 : Data.endpointOk Data.patterns[129]! = true := by decide +kernel

theorem endpoints_130 : Data.endpointOk Data.patterns[130]! = true := by decide +kernel

theorem endpoints_131 : Data.endpointOk Data.patterns[131]! = true := by decide +kernel

end Fast.Five.Checked
