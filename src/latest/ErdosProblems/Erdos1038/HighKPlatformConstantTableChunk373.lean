import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 373 through 373. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk373

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_373 :
    geometryCheck (table.cell ⟨373, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_373 :
    crossingCheck (table.cell ⟨373, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_373 :
    scalarCheck (table.cell ⟨373, by decide⟩) = true := by
  kernel_decide

theorem certificate_373 :
    Certificate (table.cell ⟨373, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_373,
    crossing_of_check crossingCheck_373,
    scalar_of_check scalarCheck_373⟩

end Erdos1038.HighKPlatformConstantTableChunk373
