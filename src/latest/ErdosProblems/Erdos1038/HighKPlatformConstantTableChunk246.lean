import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 246 through 246. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk246

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_246 :
    geometryCheck (table.cell ⟨246, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_246 :
    crossingCheck (table.cell ⟨246, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_246 :
    scalarCheck (table.cell ⟨246, by decide⟩) = true := by
  kernel_decide

theorem certificate_246 :
    Certificate (table.cell ⟨246, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_246,
    crossing_of_check crossingCheck_246,
    scalar_of_check scalarCheck_246⟩

end Erdos1038.HighKPlatformConstantTableChunk246
