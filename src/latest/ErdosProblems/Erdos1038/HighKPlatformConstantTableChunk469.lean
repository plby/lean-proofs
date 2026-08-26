import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 469 through 469. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk469

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_469 :
    geometryCheck (table.cell ⟨469, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_469 :
    crossingCheck (table.cell ⟨469, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_469 :
    scalarCheck (table.cell ⟨469, by decide⟩) = true := by
  kernel_decide

theorem certificate_469 :
    Certificate (table.cell ⟨469, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_469,
    crossing_of_check crossingCheck_469,
    scalar_of_check scalarCheck_469⟩

end Erdos1038.HighKPlatformConstantTableChunk469
