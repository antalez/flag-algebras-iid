import Fast.Five.AssembledCheck
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Fast.Five.AssemblyChecked
theorem pattern211 : assembledOk Data.patterns[211]! = true := by decide +kernel
end Fast.Five.AssemblyChecked
