import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_72 : Data.endpointOk Data.patterns[72]! = true := by decide +kernel

theorem endpoints_73 : Data.endpointOk Data.patterns[73]! = true := by decide +kernel

theorem endpoints_74 : Data.endpointOk Data.patterns[74]! = true := by decide +kernel

theorem endpoints_75 : Data.endpointOk Data.patterns[75]! = true := by decide +kernel

end Fast.Five.Checked
