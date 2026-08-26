import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 268 through 268. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk268

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_268 :
    geometryCheck (table.cell ⟨268, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_268 :
    crossingCheck (table.cell ⟨268, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_268 :
    scalarCheck (table.cell ⟨268, by decide⟩) = true := by
  kernel_decide

theorem certificate_268 :
    Certificate (table.cell ⟨268, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_268,
    crossing_of_check crossingCheck_268,
    scalar_of_check scalarCheck_268⟩

end Erdos1038.HighKPlatformConstantTableChunk268
