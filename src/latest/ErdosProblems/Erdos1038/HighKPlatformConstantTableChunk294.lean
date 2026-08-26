import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 294 through 294. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk294

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_294 :
    geometryCheck (table.cell ⟨294, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_294 :
    crossingCheck (table.cell ⟨294, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_294 :
    scalarCheck (table.cell ⟨294, by decide⟩) = true := by
  kernel_decide

theorem certificate_294 :
    Certificate (table.cell ⟨294, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_294,
    crossing_of_check crossingCheck_294,
    scalar_of_check scalarCheck_294⟩

end Erdos1038.HighKPlatformConstantTableChunk294
