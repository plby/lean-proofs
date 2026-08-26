import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 665 through 665. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk665

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_665 :
    geometryCheck (table.cell ⟨665, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_665 :
    crossingCheck (table.cell ⟨665, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_665 :
    scalarCheck (table.cell ⟨665, by decide⟩) = true := by
  kernel_decide

theorem certificate_665 :
    Certificate (table.cell ⟨665, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_665,
    crossing_of_check crossingCheck_665,
    scalar_of_check scalarCheck_665⟩

end Erdos1038.HighKPlatformConstantTableChunk665
