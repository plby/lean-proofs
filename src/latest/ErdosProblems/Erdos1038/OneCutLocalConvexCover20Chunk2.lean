import ErdosProblems.Erdos1038.OneCutLocalConvexCover20
import ErdosProblems.Erdos1038.KernelDecision

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.OneCutLocalConvexCover20

theorem localCoverChunk2_certified :
    NewtonBulkBox.SecondPositiveCoverCertified 80 6
      (266030957619458 / 10 ^ 16) (257417208359211 / 10 ^ 16)
      ((localBoxes.drop 10).take 5) := by
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  refine ⟨by kernel_decide, by kernel_decide, ?_⟩
  kernel_decide

end Erdos1038.OneCutLocalConvexCover20
