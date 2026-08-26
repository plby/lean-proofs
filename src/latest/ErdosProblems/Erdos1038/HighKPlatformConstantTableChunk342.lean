import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 342 through 342. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk342

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_342 :
    geometryCheck (table.cell ⟨342, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_342 :
    crossingCheck (table.cell ⟨342, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_342 :
    scalarCheck (table.cell ⟨342, by decide⟩) = true := by
  kernel_decide

theorem certificate_342 :
    Certificate (table.cell ⟨342, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_342,
    crossing_of_check crossingCheck_342,
    scalar_of_check scalarCheck_342⟩

end Erdos1038.HighKPlatformConstantTableChunk342
