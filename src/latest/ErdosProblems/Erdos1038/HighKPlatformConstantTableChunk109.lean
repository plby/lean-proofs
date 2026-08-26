import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 109 through 109. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk109

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_109 :
    geometryCheck (table.cell ⟨109, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_109 :
    crossingCheck (table.cell ⟨109, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_109 :
    scalarCheck (table.cell ⟨109, by decide⟩) = true := by
  kernel_decide

theorem certificate_109 :
    Certificate (table.cell ⟨109, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_109,
    crossing_of_check crossingCheck_109,
    scalar_of_check scalarCheck_109⟩

end Erdos1038.HighKPlatformConstantTableChunk109
