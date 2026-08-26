import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 492 through 492. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk492

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_492 :
    geometryCheck (table.cell ⟨492, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_492 :
    crossingCheck (table.cell ⟨492, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_492 :
    scalarCheck (table.cell ⟨492, by decide⟩) = true := by
  kernel_decide

theorem certificate_492 :
    Certificate (table.cell ⟨492, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_492,
    crossing_of_check crossingCheck_492,
    scalar_of_check scalarCheck_492⟩

end Erdos1038.HighKPlatformConstantTableChunk492
