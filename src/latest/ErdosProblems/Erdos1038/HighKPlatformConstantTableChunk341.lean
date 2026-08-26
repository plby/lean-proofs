import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 341 through 341. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk341

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_341 :
    geometryCheck (table.cell ⟨341, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_341 :
    crossingCheck (table.cell ⟨341, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_341 :
    scalarCheck (table.cell ⟨341, by decide⟩) = true := by
  kernel_decide

theorem certificate_341 :
    Certificate (table.cell ⟨341, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_341,
    crossing_of_check crossingCheck_341,
    scalar_of_check scalarCheck_341⟩

end Erdos1038.HighKPlatformConstantTableChunk341
