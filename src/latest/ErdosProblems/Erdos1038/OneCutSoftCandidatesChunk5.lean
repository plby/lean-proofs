import ErdosProblems.Erdos1038.OneCutSoftCandidates
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
open IntervalExpr
namespace OneCutSoftCandidates

theorem positiveCoverChunk5_certified :
    SoftBox.PositiveCoverCertified 32 (box29.q.hi) (box24.q.hi) ((boxes.drop 25).take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end OneCutSoftCandidates
end
end Erdos1038

