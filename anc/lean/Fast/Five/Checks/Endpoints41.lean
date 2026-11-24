import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_164 : Data.endpointOk Data.patterns[164]! = true := by decide +kernel

theorem endpoints_165 : Data.endpointOk Data.patterns[165]! = true := by decide +kernel

theorem endpoints_166 : Data.endpointOk Data.patterns[166]! = true := by decide +kernel

theorem endpoints_167 : Data.endpointOk Data.patterns[167]! = true := by decide +kernel

end Fast.Five.Checked
