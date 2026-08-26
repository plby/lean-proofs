import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 594 through 594. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk594

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_594 :
    geometryCheck (table.cell ⟨594, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_594 :
    crossingCheck (table.cell ⟨594, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_594 :
    scalarCheck (table.cell ⟨594, by decide⟩) = true := by
  kernel_decide

theorem certificate_594 :
    Certificate (table.cell ⟨594, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_594,
    crossing_of_check crossingCheck_594,
    scalar_of_check scalarCheck_594⟩

end Erdos1038.HighKPlatformConstantTableChunk594
