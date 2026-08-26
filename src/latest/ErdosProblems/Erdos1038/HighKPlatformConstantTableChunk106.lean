import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 106 through 106. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk106

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_106 :
    geometryCheck (table.cell ⟨106, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_106 :
    crossingCheck (table.cell ⟨106, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_106 :
    scalarCheck (table.cell ⟨106, by decide⟩) = true := by
  kernel_decide

theorem certificate_106 :
    Certificate (table.cell ⟨106, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_106,
    crossing_of_check crossingCheck_106,
    scalar_of_check scalarCheck_106⟩

end Erdos1038.HighKPlatformConstantTableChunk106
