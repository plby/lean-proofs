import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 418 through 418. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk418

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_418 :
    geometryCheck (table.cell ⟨418, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_418 :
    crossingCheck (table.cell ⟨418, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_418 :
    scalarCheck (table.cell ⟨418, by decide⟩) = true := by
  kernel_decide

theorem certificate_418 :
    Certificate (table.cell ⟨418, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_418,
    crossing_of_check crossingCheck_418,
    scalar_of_check scalarCheck_418⟩

end Erdos1038.HighKPlatformConstantTableChunk418
