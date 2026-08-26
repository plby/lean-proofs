import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 61 through 61. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk61

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_061 :
    geometryCheck (table.cell ⟨61, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_061 :
    crossingCheck (table.cell ⟨61, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_061 :
    scalarCheck (table.cell ⟨61, by decide⟩) = true := by
  kernel_decide

theorem certificate_061 :
    Certificate (table.cell ⟨61, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_061,
    crossing_of_check crossingCheck_061,
    scalar_of_check scalarCheck_061⟩

end Erdos1038.HighKPlatformConstantTableChunk61
