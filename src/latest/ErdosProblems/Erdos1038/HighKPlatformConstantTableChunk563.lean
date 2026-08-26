import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 563 through 563. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk563

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_563 :
    geometryCheck (table.cell ⟨563, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_563 :
    crossingCheck (table.cell ⟨563, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_563 :
    scalarCheck (table.cell ⟨563, by decide⟩) = true := by
  kernel_decide

theorem certificate_563 :
    Certificate (table.cell ⟨563, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_563,
    crossing_of_check crossingCheck_563,
    scalar_of_check scalarCheck_563⟩

end Erdos1038.HighKPlatformConstantTableChunk563
