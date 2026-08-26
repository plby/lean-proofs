import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 426 through 426. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk426

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_426 :
    geometryCheck (table.cell ⟨426, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_426 :
    crossingCheck (table.cell ⟨426, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_426 :
    scalarCheck (table.cell ⟨426, by decide⟩) = true := by
  kernel_decide

theorem certificate_426 :
    Certificate (table.cell ⟨426, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_426,
    crossing_of_check crossingCheck_426,
    scalar_of_check scalarCheck_426⟩

end Erdos1038.HighKPlatformConstantTableChunk426
