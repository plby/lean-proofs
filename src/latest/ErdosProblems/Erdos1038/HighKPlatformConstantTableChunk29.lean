import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 29 through 29. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk29

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_029 :
    geometryCheck (table.cell ⟨29, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_029 :
    crossingCheck (table.cell ⟨29, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_029 :
    scalarCheck (table.cell ⟨29, by decide⟩) = true := by
  kernel_decide

theorem certificate_029 :
    Certificate (table.cell ⟨29, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_029,
    crossing_of_check crossingCheck_029,
    scalar_of_check scalarCheck_029⟩

end Erdos1038.HighKPlatformConstantTableChunk29
