import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 652 through 652. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk652

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_652 :
    geometryCheck (table.cell ⟨652, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_652 :
    crossingCheck (table.cell ⟨652, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_652 :
    scalarCheck (table.cell ⟨652, by decide⟩) = true := by
  kernel_decide

theorem certificate_652 :
    Certificate (table.cell ⟨652, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_652,
    crossing_of_check crossingCheck_652,
    scalar_of_check scalarCheck_652⟩

end Erdos1038.HighKPlatformConstantTableChunk652
