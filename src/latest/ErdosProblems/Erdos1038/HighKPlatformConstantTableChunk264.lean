import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 264 through 264. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk264

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_264 :
    geometryCheck (table.cell ⟨264, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_264 :
    crossingCheck (table.cell ⟨264, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_264 :
    scalarCheck (table.cell ⟨264, by decide⟩) = true := by
  kernel_decide

theorem certificate_264 :
    Certificate (table.cell ⟨264, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_264,
    crossing_of_check crossingCheck_264,
    scalar_of_check scalarCheck_264⟩

end Erdos1038.HighKPlatformConstantTableChunk264
