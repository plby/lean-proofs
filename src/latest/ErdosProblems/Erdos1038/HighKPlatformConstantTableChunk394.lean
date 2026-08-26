import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 394 through 394. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk394

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_394 :
    geometryCheck (table.cell ⟨394, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_394 :
    crossingCheck (table.cell ⟨394, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_394 :
    scalarCheck (table.cell ⟨394, by decide⟩) = true := by
  kernel_decide

theorem certificate_394 :
    Certificate (table.cell ⟨394, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_394,
    crossing_of_check crossingCheck_394,
    scalar_of_check scalarCheck_394⟩

end Erdos1038.HighKPlatformConstantTableChunk394
