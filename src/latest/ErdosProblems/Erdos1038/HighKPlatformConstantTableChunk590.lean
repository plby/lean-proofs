import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 590 through 590. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk590

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_590 :
    geometryCheck (table.cell ⟨590, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_590 :
    crossingCheck (table.cell ⟨590, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_590 :
    scalarCheck (table.cell ⟨590, by decide⟩) = true := by
  kernel_decide

theorem certificate_590 :
    Certificate (table.cell ⟨590, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_590,
    crossing_of_check crossingCheck_590,
    scalar_of_check scalarCheck_590⟩

end Erdos1038.HighKPlatformConstantTableChunk590
