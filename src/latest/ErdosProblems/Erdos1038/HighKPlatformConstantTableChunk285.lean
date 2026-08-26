import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 285 through 285. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk285

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_285 :
    geometryCheck (table.cell ⟨285, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_285 :
    crossingCheck (table.cell ⟨285, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_285 :
    scalarCheck (table.cell ⟨285, by decide⟩) = true := by
  kernel_decide

theorem certificate_285 :
    Certificate (table.cell ⟨285, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_285,
    crossing_of_check crossingCheck_285,
    scalar_of_check scalarCheck_285⟩

end Erdos1038.HighKPlatformConstantTableChunk285
