import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 626 through 626. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk626

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_626 :
    geometryCheck (table.cell ⟨626, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_626 :
    crossingCheck (table.cell ⟨626, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_626 :
    scalarCheck (table.cell ⟨626, by decide⟩) = true := by
  kernel_decide

theorem certificate_626 :
    Certificate (table.cell ⟨626, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_626,
    crossing_of_check crossingCheck_626,
    scalar_of_check scalarCheck_626⟩

end Erdos1038.HighKPlatformConstantTableChunk626
