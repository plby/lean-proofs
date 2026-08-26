import ErdosProblems.Erdos1038.OneCutLocalConvexCover20
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.OneCutLocalConvexCover20

theorem localCoverChunk0_certified :
    NewtonBulkBox.SecondPositiveCoverCertified 80 6
      (248803459098964 / 10 ^ 16) localStart (localBoxes.take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end Erdos1038.OneCutLocalConvexCover20
