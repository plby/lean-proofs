import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 380 through 380. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk380

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_380 :
    geometryCheck (table.cell ⟨380, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_380 :
    crossingCheck (table.cell ⟨380, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_380 :
    scalarCheck (table.cell ⟨380, by decide⟩) = true := by
  kernel_decide

theorem certificate_380 :
    Certificate (table.cell ⟨380, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_380,
    crossing_of_check crossingCheck_380,
    scalar_of_check scalarCheck_380⟩

end Erdos1038.HighKPlatformConstantTableChunk380
