import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 531 through 531. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk531

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_531 :
    geometryCheck (table.cell ⟨531, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_531 :
    crossingCheck (table.cell ⟨531, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_531 :
    scalarCheck (table.cell ⟨531, by decide⟩) = true := by
  kernel_decide

theorem certificate_531 :
    Certificate (table.cell ⟨531, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_531,
    crossing_of_check crossingCheck_531,
    scalar_of_check scalarCheck_531⟩

end Erdos1038.HighKPlatformConstantTableChunk531
