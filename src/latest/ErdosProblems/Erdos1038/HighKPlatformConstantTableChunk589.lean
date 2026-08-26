import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 589 through 589. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk589

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_589 :
    geometryCheck (table.cell ⟨589, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_589 :
    crossingCheck (table.cell ⟨589, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_589 :
    scalarCheck (table.cell ⟨589, by decide⟩) = true := by
  kernel_decide

theorem certificate_589 :
    Certificate (table.cell ⟨589, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_589,
    crossing_of_check crossingCheck_589,
    scalar_of_check scalarCheck_589⟩

end Erdos1038.HighKPlatformConstantTableChunk589
