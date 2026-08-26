import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 458 through 458. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk458

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_458 :
    geometryCheck (table.cell ⟨458, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_458 :
    crossingCheck (table.cell ⟨458, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_458 :
    scalarCheck (table.cell ⟨458, by decide⟩) = true := by
  kernel_decide

theorem certificate_458 :
    Certificate (table.cell ⟨458, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_458,
    crossing_of_check crossingCheck_458,
    scalar_of_check scalarCheck_458⟩

end Erdos1038.HighKPlatformConstantTableChunk458
