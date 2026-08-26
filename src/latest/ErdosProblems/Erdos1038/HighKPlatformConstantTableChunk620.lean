import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 620 through 620. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk620

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_620 :
    geometryCheck (table.cell ⟨620, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_620 :
    crossingCheck (table.cell ⟨620, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_620 :
    scalarCheck (table.cell ⟨620, by decide⟩) = true := by
  kernel_decide

theorem certificate_620 :
    Certificate (table.cell ⟨620, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_620,
    crossing_of_check crossingCheck_620,
    scalar_of_check scalarCheck_620⟩

end Erdos1038.HighKPlatformConstantTableChunk620
