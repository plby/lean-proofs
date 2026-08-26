import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 656 through 656. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk656

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_656 :
    geometryCheck (table.cell ⟨656, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_656 :
    crossingCheck (table.cell ⟨656, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_656 :
    scalarCheck (table.cell ⟨656, by decide⟩) = true := by
  kernel_decide

theorem certificate_656 :
    Certificate (table.cell ⟨656, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_656,
    crossing_of_check crossingCheck_656,
    scalar_of_check scalarCheck_656⟩

end Erdos1038.HighKPlatformConstantTableChunk656
