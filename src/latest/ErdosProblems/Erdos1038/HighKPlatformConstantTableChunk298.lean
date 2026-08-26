import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 298 through 298. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk298

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_298 :
    geometryCheck (table.cell ⟨298, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_298 :
    crossingCheck (table.cell ⟨298, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_298 :
    scalarCheck (table.cell ⟨298, by decide⟩) = true := by
  kernel_decide

theorem certificate_298 :
    Certificate (table.cell ⟨298, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_298,
    crossing_of_check crossingCheck_298,
    scalar_of_check scalarCheck_298⟩

end Erdos1038.HighKPlatformConstantTableChunk298
