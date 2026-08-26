import ErdosProblems.Erdos1038.OneCutSoftCandidates
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
open IntervalExpr
namespace OneCutSoftCandidates

theorem positiveCoverChunk22_certified :
    SoftBox.PositiveCoverCertified 32 (box114.q.hi) (box109.q.hi) ((boxes.drop 110).take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end OneCutSoftCandidates
end
end Erdos1038

