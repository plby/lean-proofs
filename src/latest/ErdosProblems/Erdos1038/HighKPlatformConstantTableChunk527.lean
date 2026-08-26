import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 527 through 527. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk527

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_527 :
    geometryCheck (table.cell ⟨527, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_527 :
    crossingCheck (table.cell ⟨527, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_527 :
    scalarCheck (table.cell ⟨527, by decide⟩) = true := by
  kernel_decide

theorem certificate_527 :
    Certificate (table.cell ⟨527, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_527,
    crossing_of_check crossingCheck_527,
    scalar_of_check scalarCheck_527⟩

end Erdos1038.HighKPlatformConstantTableChunk527
