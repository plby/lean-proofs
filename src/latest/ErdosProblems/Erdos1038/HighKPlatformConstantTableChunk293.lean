import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 293 through 293. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk293

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_293 :
    geometryCheck (table.cell ⟨293, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_293 :
    crossingCheck (table.cell ⟨293, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_293 :
    scalarCheck (table.cell ⟨293, by decide⟩) = true := by
  kernel_decide

theorem certificate_293 :
    Certificate (table.cell ⟨293, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_293,
    crossing_of_check crossingCheck_293,
    scalar_of_check scalarCheck_293⟩

end Erdos1038.HighKPlatformConstantTableChunk293
