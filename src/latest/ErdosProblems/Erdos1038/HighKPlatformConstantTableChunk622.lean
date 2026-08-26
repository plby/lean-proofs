import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 622 through 622. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk622

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_622 :
    geometryCheck (table.cell ⟨622, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_622 :
    crossingCheck (table.cell ⟨622, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_622 :
    scalarCheck (table.cell ⟨622, by decide⟩) = true := by
  kernel_decide

theorem certificate_622 :
    Certificate (table.cell ⟨622, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_622,
    crossing_of_check crossingCheck_622,
    scalar_of_check scalarCheck_622⟩

end Erdos1038.HighKPlatformConstantTableChunk622
