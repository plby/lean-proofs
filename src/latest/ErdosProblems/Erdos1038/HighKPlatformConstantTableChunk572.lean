import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 572 through 572. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk572

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_572 :
    geometryCheck (table.cell ⟨572, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_572 :
    crossingCheck (table.cell ⟨572, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_572 :
    scalarCheck (table.cell ⟨572, by decide⟩) = true := by
  kernel_decide

theorem certificate_572 :
    Certificate (table.cell ⟨572, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_572,
    crossing_of_check crossingCheck_572,
    scalar_of_check scalarCheck_572⟩

end Erdos1038.HighKPlatformConstantTableChunk572
