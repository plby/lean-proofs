import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 603 through 603. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk603

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_603 :
    geometryCheck (table.cell ⟨603, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_603 :
    crossingCheck (table.cell ⟨603, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_603 :
    scalarCheck (table.cell ⟨603, by decide⟩) = true := by
  kernel_decide

theorem certificate_603 :
    Certificate (table.cell ⟨603, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_603,
    crossing_of_check crossingCheck_603,
    scalar_of_check scalarCheck_603⟩

end Erdos1038.HighKPlatformConstantTableChunk603
