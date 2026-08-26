import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 561 through 561. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk561

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_561 :
    geometryCheck (table.cell ⟨561, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_561 :
    crossingCheck (table.cell ⟨561, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_561 :
    scalarCheck (table.cell ⟨561, by decide⟩) = true := by
  kernel_decide

theorem certificate_561 :
    Certificate (table.cell ⟨561, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_561,
    crossing_of_check crossingCheck_561,
    scalar_of_check scalarCheck_561⟩

end Erdos1038.HighKPlatformConstantTableChunk561
