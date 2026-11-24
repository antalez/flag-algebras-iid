import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_224 : Data.endpointOk Data.patterns[224]! = true := by decide +kernel

theorem endpoints_225 : Data.endpointOk Data.patterns[225]! = true := by decide +kernel

theorem endpoints_226 : Data.endpointOk Data.patterns[226]! = true := by decide +kernel

theorem endpoints_227 : Data.endpointOk Data.patterns[227]! = true := by decide +kernel

end Fast.Five.Checked
