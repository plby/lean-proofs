import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 155 through 155. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk155

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_155 :
    geometryCheck (table.cell ⟨155, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_155 :
    crossingCheck (table.cell ⟨155, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_155 :
    scalarCheck (table.cell ⟨155, by decide⟩) = true := by
  kernel_decide

theorem certificate_155 :
    Certificate (table.cell ⟨155, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_155,
    crossing_of_check crossingCheck_155,
    scalar_of_check scalarCheck_155⟩

end Erdos1038.HighKPlatformConstantTableChunk155
