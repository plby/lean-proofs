import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 329 through 329. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk329

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_329 :
    geometryCheck (table.cell ⟨329, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_329 :
    crossingCheck (table.cell ⟨329, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_329 :
    scalarCheck (table.cell ⟨329, by decide⟩) = true := by
  kernel_decide

theorem certificate_329 :
    Certificate (table.cell ⟨329, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_329,
    crossing_of_check crossingCheck_329,
    scalar_of_check scalarCheck_329⟩

end Erdos1038.HighKPlatformConstantTableChunk329
