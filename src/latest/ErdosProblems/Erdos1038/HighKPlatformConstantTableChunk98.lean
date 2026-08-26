import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 98 through 98. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk98

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_098 :
    geometryCheck (table.cell ⟨98, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_098 :
    crossingCheck (table.cell ⟨98, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_098 :
    scalarCheck (table.cell ⟨98, by decide⟩) = true := by
  kernel_decide

theorem certificate_098 :
    Certificate (table.cell ⟨98, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_098,
    crossing_of_check crossingCheck_098,
    scalar_of_check scalarCheck_098⟩

end Erdos1038.HighKPlatformConstantTableChunk98
