import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 477 through 477. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk477

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_477 :
    geometryCheck (table.cell ⟨477, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_477 :
    crossingCheck (table.cell ⟨477, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_477 :
    scalarCheck (table.cell ⟨477, by decide⟩) = true := by
  kernel_decide

theorem certificate_477 :
    Certificate (table.cell ⟨477, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_477,
    crossing_of_check crossingCheck_477,
    scalar_of_check scalarCheck_477⟩

end Erdos1038.HighKPlatformConstantTableChunk477
