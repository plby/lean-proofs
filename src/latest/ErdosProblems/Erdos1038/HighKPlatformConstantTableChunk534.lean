import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 534 through 534. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk534

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_534 :
    geometryCheck (table.cell ⟨534, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_534 :
    crossingCheck (table.cell ⟨534, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_534 :
    scalarCheck (table.cell ⟨534, by decide⟩) = true := by
  kernel_decide

theorem certificate_534 :
    Certificate (table.cell ⟨534, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_534,
    crossing_of_check crossingCheck_534,
    scalar_of_check scalarCheck_534⟩

end Erdos1038.HighKPlatformConstantTableChunk534
