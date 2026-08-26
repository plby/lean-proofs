import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 494 through 494. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk494

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_494 :
    geometryCheck (table.cell ⟨494, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_494 :
    crossingCheck (table.cell ⟨494, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_494 :
    scalarCheck (table.cell ⟨494, by decide⟩) = true := by
  kernel_decide

theorem certificate_494 :
    Certificate (table.cell ⟨494, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_494,
    crossing_of_check crossingCheck_494,
    scalar_of_check scalarCheck_494⟩

end Erdos1038.HighKPlatformConstantTableChunk494
