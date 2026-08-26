import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 38 through 38. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk38

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_038 :
    geometryCheck (table.cell ⟨38, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_038 :
    crossingCheck (table.cell ⟨38, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_038 :
    scalarCheck (table.cell ⟨38, by decide⟩) = true := by
  kernel_decide

theorem certificate_038 :
    Certificate (table.cell ⟨38, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_038,
    crossing_of_check crossingCheck_038,
    scalar_of_check scalarCheck_038⟩

end Erdos1038.HighKPlatformConstantTableChunk38
