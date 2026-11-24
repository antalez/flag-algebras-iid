import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_252 : Data.endpointOk Data.patterns[252]! = true := by decide +kernel

theorem endpoints_253 : Data.endpointOk Data.patterns[253]! = true := by decide +kernel

theorem endpoints_254 : Data.endpointOk Data.patterns[254]! = true := by decide +kernel

theorem endpoints_255 : Data.endpointOk Data.patterns[255]! = true := by decide +kernel

end Fast.Five.Checked
