import ErdosProblems.Erdos1038.OneCutLocalConvexCover20
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.OneCutLocalConvexCover20

theorem localCoverChunk1_certified :
    NewtonBulkBox.SecondPositiveCoverCertified 80 6
      (257417208359211 / 10 ^ 16) (248803459098964 / 10 ^ 16)
      ((localBoxes.drop 5).take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end Erdos1038.OneCutLocalConvexCover20
