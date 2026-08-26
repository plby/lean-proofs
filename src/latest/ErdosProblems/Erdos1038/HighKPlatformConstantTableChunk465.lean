import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 465 through 465. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk465

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_465 :
    geometryCheck (table.cell ⟨465, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_465 :
    crossingCheck (table.cell ⟨465, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_465 :
    scalarCheck (table.cell ⟨465, by decide⟩) = true := by
  kernel_decide

theorem certificate_465 :
    Certificate (table.cell ⟨465, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_465,
    crossing_of_check crossingCheck_465,
    scalar_of_check scalarCheck_465⟩

end Erdos1038.HighKPlatformConstantTableChunk465
