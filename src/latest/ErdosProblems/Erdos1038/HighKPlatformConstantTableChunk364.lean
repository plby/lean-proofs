import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 364 through 364. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk364

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_364 :
    geometryCheck (table.cell ⟨364, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_364 :
    crossingCheck (table.cell ⟨364, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_364 :
    scalarCheck (table.cell ⟨364, by decide⟩) = true := by
  kernel_decide

theorem certificate_364 :
    Certificate (table.cell ⟨364, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_364,
    crossing_of_check crossingCheck_364,
    scalar_of_check scalarCheck_364⟩

end Erdos1038.HighKPlatformConstantTableChunk364
