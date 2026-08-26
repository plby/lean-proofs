import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 358 through 358. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk358

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_358 :
    geometryCheck (table.cell ⟨358, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_358 :
    crossingCheck (table.cell ⟨358, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_358 :
    scalarCheck (table.cell ⟨358, by decide⟩) = true := by
  kernel_decide

theorem certificate_358 :
    Certificate (table.cell ⟨358, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_358,
    crossing_of_check crossingCheck_358,
    scalar_of_check scalarCheck_358⟩

end Erdos1038.HighKPlatformConstantTableChunk358
