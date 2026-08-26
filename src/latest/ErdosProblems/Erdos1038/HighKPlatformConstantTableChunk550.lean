import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 550 through 550. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk550

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_550 :
    geometryCheck (table.cell ⟨550, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_550 :
    crossingCheck (table.cell ⟨550, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_550 :
    scalarCheck (table.cell ⟨550, by decide⟩) = true := by
  kernel_decide

theorem certificate_550 :
    Certificate (table.cell ⟨550, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_550,
    crossing_of_check crossingCheck_550,
    scalar_of_check scalarCheck_550⟩

end Erdos1038.HighKPlatformConstantTableChunk550
