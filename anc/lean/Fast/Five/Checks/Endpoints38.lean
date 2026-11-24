import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_152 : Data.endpointOk Data.patterns[152]! = true := by decide +kernel

theorem endpoints_153 : Data.endpointOk Data.patterns[153]! = true := by decide +kernel

theorem endpoints_154 : Data.endpointOk Data.patterns[154]! = true := by decide +kernel

theorem endpoints_155 : Data.endpointOk Data.patterns[155]! = true := by decide +kernel

end Fast.Five.Checked
