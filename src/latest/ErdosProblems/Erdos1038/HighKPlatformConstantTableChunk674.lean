import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 674 through 674. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk674

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_674 :
    geometryCheck (table.cell ⟨674, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_674 :
    crossingCheck (table.cell ⟨674, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_674 :
    scalarCheck (table.cell ⟨674, by decide⟩) = true := by
  kernel_decide

theorem certificate_674 :
    Certificate (table.cell ⟨674, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_674,
    crossing_of_check crossingCheck_674,
    scalar_of_check scalarCheck_674⟩

end Erdos1038.HighKPlatformConstantTableChunk674
