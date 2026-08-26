import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 503 through 503. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk503

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_503 :
    geometryCheck (table.cell ⟨503, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_503 :
    crossingCheck (table.cell ⟨503, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_503 :
    scalarCheck (table.cell ⟨503, by decide⟩) = true := by
  kernel_decide

theorem certificate_503 :
    Certificate (table.cell ⟨503, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_503,
    crossing_of_check crossingCheck_503,
    scalar_of_check scalarCheck_503⟩

end Erdos1038.HighKPlatformConstantTableChunk503
