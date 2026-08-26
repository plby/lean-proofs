import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 351 through 351. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk351

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_351 :
    geometryCheck (table.cell ⟨351, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_351 :
    crossingCheck (table.cell ⟨351, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_351 :
    scalarCheck (table.cell ⟨351, by decide⟩) = true := by
  kernel_decide

theorem certificate_351 :
    Certificate (table.cell ⟨351, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_351,
    crossing_of_check crossingCheck_351,
    scalar_of_check scalarCheck_351⟩

end Erdos1038.HighKPlatformConstantTableChunk351
