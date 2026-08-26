import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 113 through 113. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk113

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_113 :
    geometryCheck (table.cell ⟨113, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_113 :
    crossingCheck (table.cell ⟨113, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_113 :
    scalarCheck (table.cell ⟨113, by decide⟩) = true := by
  kernel_decide

theorem certificate_113 :
    Certificate (table.cell ⟨113, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_113,
    crossing_of_check crossingCheck_113,
    scalar_of_check scalarCheck_113⟩

end Erdos1038.HighKPlatformConstantTableChunk113
