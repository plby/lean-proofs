import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 254 through 254. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk254

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_254 :
    geometryCheck (table.cell ⟨254, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_254 :
    crossingCheck (table.cell ⟨254, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_254 :
    scalarCheck (table.cell ⟨254, by decide⟩) = true := by
  kernel_decide

theorem certificate_254 :
    Certificate (table.cell ⟨254, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_254,
    crossing_of_check crossingCheck_254,
    scalar_of_check scalarCheck_254⟩

end Erdos1038.HighKPlatformConstantTableChunk254
