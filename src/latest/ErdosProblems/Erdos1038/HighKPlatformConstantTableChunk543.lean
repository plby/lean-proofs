import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 543 through 543. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk543

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_543 :
    geometryCheck (table.cell ⟨543, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_543 :
    crossingCheck (table.cell ⟨543, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_543 :
    scalarCheck (table.cell ⟨543, by decide⟩) = true := by
  kernel_decide

theorem certificate_543 :
    Certificate (table.cell ⟨543, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_543,
    crossing_of_check crossingCheck_543,
    scalar_of_check scalarCheck_543⟩

end Erdos1038.HighKPlatformConstantTableChunk543
