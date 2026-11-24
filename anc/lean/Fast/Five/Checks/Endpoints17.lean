import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_68 : Data.endpointOk Data.patterns[68]! = true := by decide +kernel

theorem endpoints_69 : Data.endpointOk Data.patterns[69]! = true := by decide +kernel

theorem endpoints_70 : Data.endpointOk Data.patterns[70]! = true := by decide +kernel

theorem endpoints_71 : Data.endpointOk Data.patterns[71]! = true := by decide +kernel

end Fast.Five.Checked
