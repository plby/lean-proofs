import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 607 through 607. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk607

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_607 :
    geometryCheck (table.cell ⟨607, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_607 :
    crossingCheck (table.cell ⟨607, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_607 :
    scalarCheck (table.cell ⟨607, by decide⟩) = true := by
  kernel_decide

theorem certificate_607 :
    Certificate (table.cell ⟨607, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_607,
    crossing_of_check crossingCheck_607,
    scalar_of_check scalarCheck_607⟩

end Erdos1038.HighKPlatformConstantTableChunk607
