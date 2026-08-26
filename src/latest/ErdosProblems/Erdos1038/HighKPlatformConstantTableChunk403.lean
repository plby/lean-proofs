import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 403 through 403. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk403

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_403 :
    geometryCheck (table.cell ⟨403, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_403 :
    crossingCheck (table.cell ⟨403, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_403 :
    scalarCheck (table.cell ⟨403, by decide⟩) = true := by
  kernel_decide

theorem certificate_403 :
    Certificate (table.cell ⟨403, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_403,
    crossing_of_check crossingCheck_403,
    scalar_of_check scalarCheck_403⟩

end Erdos1038.HighKPlatformConstantTableChunk403
