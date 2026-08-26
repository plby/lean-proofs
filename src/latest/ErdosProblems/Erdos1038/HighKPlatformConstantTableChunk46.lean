import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 46 through 46. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk46

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_046 :
    geometryCheck (table.cell ⟨46, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_046 :
    crossingCheck (table.cell ⟨46, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_046 :
    scalarCheck (table.cell ⟨46, by decide⟩) = true := by
  kernel_decide

theorem certificate_046 :
    Certificate (table.cell ⟨46, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_046,
    crossing_of_check crossingCheck_046,
    scalar_of_check scalarCheck_046⟩

end Erdos1038.HighKPlatformConstantTableChunk46
