import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 274 through 274. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk274

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_274 :
    geometryCheck (table.cell ⟨274, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_274 :
    crossingCheck (table.cell ⟨274, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_274 :
    scalarCheck (table.cell ⟨274, by decide⟩) = true := by
  kernel_decide

theorem certificate_274 :
    Certificate (table.cell ⟨274, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_274,
    crossing_of_check crossingCheck_274,
    scalar_of_check scalarCheck_274⟩

end Erdos1038.HighKPlatformConstantTableChunk274
