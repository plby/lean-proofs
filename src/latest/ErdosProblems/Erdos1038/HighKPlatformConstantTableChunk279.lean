import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 279 through 279. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk279

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_279 :
    geometryCheck (table.cell ⟨279, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_279 :
    crossingCheck (table.cell ⟨279, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_279 :
    scalarCheck (table.cell ⟨279, by decide⟩) = true := by
  kernel_decide

theorem certificate_279 :
    Certificate (table.cell ⟨279, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_279,
    crossing_of_check crossingCheck_279,
    scalar_of_check scalarCheck_279⟩

end Erdos1038.HighKPlatformConstantTableChunk279
