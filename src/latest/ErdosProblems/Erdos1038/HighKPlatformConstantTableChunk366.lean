import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 366 through 366. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk366

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_366 :
    geometryCheck (table.cell ⟨366, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_366 :
    crossingCheck (table.cell ⟨366, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_366 :
    scalarCheck (table.cell ⟨366, by decide⟩) = true := by
  kernel_decide

theorem certificate_366 :
    Certificate (table.cell ⟨366, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_366,
    crossing_of_check crossingCheck_366,
    scalar_of_check scalarCheck_366⟩

end Erdos1038.HighKPlatformConstantTableChunk366
