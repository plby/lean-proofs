import ErdosProblems.Erdos1038.OneCutTailQCandidates
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038
noncomputable section
namespace OneCutTailCertificate
namespace OneCutTailQCandidates

theorem positiveCoverChunk1_certified :
    TailQBox.PositiveCoverCertified 80
      (775565240650901643543 / 25000000000000000000000) (28776681009190887054571 / 1000000000000000000000000) ((positiveBoxes.drop 5).take 5) := by
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

