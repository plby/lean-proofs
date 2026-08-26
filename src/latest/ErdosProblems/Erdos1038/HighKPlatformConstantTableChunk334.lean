import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 334 through 334. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk334

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_334 :
    geometryCheck (table.cell ⟨334, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_334 :
    crossingCheck (table.cell ⟨334, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_334 :
    scalarCheck (table.cell ⟨334, by decide⟩) = true := by
  kernel_decide

theorem certificate_334 :
    Certificate (table.cell ⟨334, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_334,
    crossing_of_check crossingCheck_334,
    scalar_of_check scalarCheck_334⟩

end Erdos1038.HighKPlatformConstantTableChunk334
