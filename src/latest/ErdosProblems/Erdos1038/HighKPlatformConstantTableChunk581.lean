import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 581 through 581. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk581

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_581 :
    geometryCheck (table.cell ⟨581, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_581 :
    crossingCheck (table.cell ⟨581, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_581 :
    scalarCheck (table.cell ⟨581, by decide⟩) = true := by
  kernel_decide

theorem certificate_581 :
    Certificate (table.cell ⟨581, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_581,
    crossing_of_check crossingCheck_581,
    scalar_of_check scalarCheck_581⟩

end Erdos1038.HighKPlatformConstantTableChunk581
