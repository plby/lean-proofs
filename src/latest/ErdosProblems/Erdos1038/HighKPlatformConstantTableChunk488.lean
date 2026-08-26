import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 488 through 488. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk488

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_488 :
    geometryCheck (table.cell ⟨488, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_488 :
    crossingCheck (table.cell ⟨488, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_488 :
    scalarCheck (table.cell ⟨488, by decide⟩) = true := by
  kernel_decide

theorem certificate_488 :
    Certificate (table.cell ⟨488, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_488,
    crossing_of_check crossingCheck_488,
    scalar_of_check scalarCheck_488⟩

end Erdos1038.HighKPlatformConstantTableChunk488
