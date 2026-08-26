import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 441 through 441. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk441

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_441 :
    geometryCheck (table.cell ⟨441, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_441 :
    crossingCheck (table.cell ⟨441, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_441 :
    scalarCheck (table.cell ⟨441, by decide⟩) = true := by
  kernel_decide

theorem certificate_441 :
    Certificate (table.cell ⟨441, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_441,
    crossing_of_check crossingCheck_441,
    scalar_of_check scalarCheck_441⟩

end Erdos1038.HighKPlatformConstantTableChunk441
