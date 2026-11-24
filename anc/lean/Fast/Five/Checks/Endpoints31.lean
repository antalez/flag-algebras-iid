import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_124 : Data.endpointOk Data.patterns[124]! = true := by decide +kernel

theorem endpoints_125 : Data.endpointOk Data.patterns[125]! = true := by decide +kernel

theorem endpoints_126 : Data.endpointOk Data.patterns[126]! = true := by decide +kernel

theorem endpoints_127 : Data.endpointOk Data.patterns[127]! = true := by decide +kernel

end Fast.Five.Checked
