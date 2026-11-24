import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_40 : Data.endpointOk Data.patterns[40]! = true := by decide +kernel

theorem endpoints_41 : Data.endpointOk Data.patterns[41]! = true := by decide +kernel

theorem endpoints_42 : Data.endpointOk Data.patterns[42]! = true := by decide +kernel

theorem endpoints_43 : Data.endpointOk Data.patterns[43]! = true := by decide +kernel

end Fast.Five.Checked
