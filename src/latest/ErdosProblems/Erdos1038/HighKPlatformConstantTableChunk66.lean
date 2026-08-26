import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 66 through 66. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk66

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_066 :
    geometryCheck (table.cell ⟨66, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_066 :
    crossingCheck (table.cell ⟨66, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_066 :
    scalarCheck (table.cell ⟨66, by decide⟩) = true := by
  kernel_decide

theorem certificate_066 :
    Certificate (table.cell ⟨66, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_066,
    crossing_of_check crossingCheck_066,
    scalar_of_check scalarCheck_066⟩

end Erdos1038.HighKPlatformConstantTableChunk66
