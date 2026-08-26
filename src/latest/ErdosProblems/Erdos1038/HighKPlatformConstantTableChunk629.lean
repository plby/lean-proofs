import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 629 through 629. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk629

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_629 :
    geometryCheck (table.cell ⟨629, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_629 :
    crossingCheck (table.cell ⟨629, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_629 :
    scalarCheck (table.cell ⟨629, by decide⟩) = true := by
  kernel_decide

theorem certificate_629 :
    Certificate (table.cell ⟨629, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_629,
    crossing_of_check crossingCheck_629,
    scalar_of_check scalarCheck_629⟩

end Erdos1038.HighKPlatformConstantTableChunk629
