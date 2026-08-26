import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 261 through 261. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk261

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_261 :
    geometryCheck (table.cell ⟨261, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_261 :
    crossingCheck (table.cell ⟨261, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_261 :
    scalarCheck (table.cell ⟨261, by decide⟩) = true := by
  kernel_decide

theorem certificate_261 :
    Certificate (table.cell ⟨261, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_261,
    crossing_of_check crossingCheck_261,
    scalar_of_check scalarCheck_261⟩

end Erdos1038.HighKPlatformConstantTableChunk261
