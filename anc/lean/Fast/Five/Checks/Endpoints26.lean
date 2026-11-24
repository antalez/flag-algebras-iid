import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_104 : Data.endpointOk Data.patterns[104]! = true := by decide +kernel

theorem endpoints_105 : Data.endpointOk Data.patterns[105]! = true := by decide +kernel

theorem endpoints_106 : Data.endpointOk Data.patterns[106]! = true := by decide +kernel

theorem endpoints_107 : Data.endpointOk Data.patterns[107]! = true := by decide +kernel

end Fast.Five.Checked
