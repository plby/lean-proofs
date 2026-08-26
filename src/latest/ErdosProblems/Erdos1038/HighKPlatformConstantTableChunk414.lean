import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 414 through 414. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk414

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_414 :
    geometryCheck (table.cell ⟨414, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_414 :
    crossingCheck (table.cell ⟨414, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_414 :
    scalarCheck (table.cell ⟨414, by decide⟩) = true := by
  kernel_decide

theorem certificate_414 :
    Certificate (table.cell ⟨414, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_414,
    crossing_of_check crossingCheck_414,
    scalar_of_check scalarCheck_414⟩

end Erdos1038.HighKPlatformConstantTableChunk414
