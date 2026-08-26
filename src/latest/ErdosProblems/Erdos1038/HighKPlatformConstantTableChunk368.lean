import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 368 through 368. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk368

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_368 :
    geometryCheck (table.cell ⟨368, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_368 :
    crossingCheck (table.cell ⟨368, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_368 :
    scalarCheck (table.cell ⟨368, by decide⟩) = true := by
  kernel_decide

theorem certificate_368 :
    Certificate (table.cell ⟨368, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_368,
    crossing_of_check crossingCheck_368,
    scalar_of_check scalarCheck_368⟩

end Erdos1038.HighKPlatformConstantTableChunk368
