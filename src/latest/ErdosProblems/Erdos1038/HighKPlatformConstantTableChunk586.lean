import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 586 through 586. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk586

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_586 :
    geometryCheck (table.cell ⟨586, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_586 :
    crossingCheck (table.cell ⟨586, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_586 :
    scalarCheck (table.cell ⟨586, by decide⟩) = true := by
  kernel_decide

theorem certificate_586 :
    Certificate (table.cell ⟨586, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_586,
    crossing_of_check crossingCheck_586,
    scalar_of_check scalarCheck_586⟩

end Erdos1038.HighKPlatformConstantTableChunk586
