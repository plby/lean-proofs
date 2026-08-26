import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 124 through 124. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk124

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_124 :
    geometryCheck (table.cell ⟨124, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_124 :
    crossingCheck (table.cell ⟨124, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_124 :
    scalarCheck (table.cell ⟨124, by decide⟩) = true := by
  kernel_decide

theorem certificate_124 :
    Certificate (table.cell ⟨124, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_124,
    crossing_of_check crossingCheck_124,
    scalar_of_check scalarCheck_124⟩

end Erdos1038.HighKPlatformConstantTableChunk124
