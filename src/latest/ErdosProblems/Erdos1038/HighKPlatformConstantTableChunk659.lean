import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 659 through 659. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk659

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_659 :
    geometryCheck (table.cell ⟨659, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_659 :
    crossingCheck (table.cell ⟨659, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_659 :
    scalarCheck (table.cell ⟨659, by decide⟩) = true := by
  kernel_decide

theorem certificate_659 :
    Certificate (table.cell ⟨659, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_659,
    crossing_of_check crossingCheck_659,
    scalar_of_check scalarCheck_659⟩

end Erdos1038.HighKPlatformConstantTableChunk659
