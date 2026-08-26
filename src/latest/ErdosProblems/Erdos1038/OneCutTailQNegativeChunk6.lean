import ErdosProblems.Erdos1038.OneCutTailQCandidates
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
namespace OneCutTailCertificate
namespace OneCutTailQCandidates

theorem negativeCoverChunk6_certified :
    TailQBox.NegativeCoverCertified 80
      (842872230729288167 / 1000000000000000000000000) (8762760818162333 / 1000000000000000000000000) ((negativeBoxes.drop 30).take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end OneCutTailQCandidates
end OneCutTailCertificate
end
end Erdos1038

