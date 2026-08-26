import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 142 through 142. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk142

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_142 :
    geometryCheck (table.cell ⟨142, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_142 :
    crossingCheck (table.cell ⟨142, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_142 :
    scalarCheck (table.cell ⟨142, by decide⟩) = true := by
  kernel_decide

theorem certificate_142 :
    Certificate (table.cell ⟨142, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_142,
    crossing_of_check crossingCheck_142,
    scalar_of_check scalarCheck_142⟩

end Erdos1038.HighKPlatformConstantTableChunk142
