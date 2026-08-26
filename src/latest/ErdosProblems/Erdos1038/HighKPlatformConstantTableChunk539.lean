import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 539 through 539. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk539

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_539 :
    geometryCheck (table.cell ⟨539, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_539 :
    crossingCheck (table.cell ⟨539, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_539 :
    scalarCheck (table.cell ⟨539, by decide⟩) = true := by
  kernel_decide

theorem certificate_539 :
    Certificate (table.cell ⟨539, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_539,
    crossing_of_check crossingCheck_539,
    scalar_of_check scalarCheck_539⟩

end Erdos1038.HighKPlatformConstantTableChunk539
