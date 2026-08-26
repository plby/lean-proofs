import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 85 through 85. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk85

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_085 :
    geometryCheck (table.cell ⟨85, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_085 :
    crossingCheck (table.cell ⟨85, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_085 :
    scalarCheck (table.cell ⟨85, by decide⟩) = true := by
  kernel_decide

theorem certificate_085 :
    Certificate (table.cell ⟨85, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_085,
    crossing_of_check crossingCheck_085,
    scalar_of_check scalarCheck_085⟩

end Erdos1038.HighKPlatformConstantTableChunk85
