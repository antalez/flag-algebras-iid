import Fast.Five.Data

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem endpoints_268 : Data.endpointOk Data.patterns[268]! = true := by decide +kernel

theorem endpoints_269 : Data.endpointOk Data.patterns[269]! = true := by decide +kernel

theorem endpoints_270 : Data.endpointOk Data.patterns[270]! = true := by decide +kernel

theorem endpoints_271 : Data.endpointOk Data.patterns[271]! = true := by decide +kernel

end Fast.Five.Checked
