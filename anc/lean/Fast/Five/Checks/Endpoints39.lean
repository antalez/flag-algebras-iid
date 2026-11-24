import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_156 : Data.endpointOk Data.patterns[156]! = true := by decide +kernel

theorem endpoints_157 : Data.endpointOk Data.patterns[157]! = true := by decide +kernel

theorem endpoints_158 : Data.endpointOk Data.patterns[158]! = true := by decide +kernel

theorem endpoints_159 : Data.endpointOk Data.patterns[159]! = true := by decide +kernel

end Fast.Five.Checked
