import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 129 through 129. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk129

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_129 :
    geometryCheck (table.cell ⟨129, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_129 :
    crossingCheck (table.cell ⟨129, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_129 :
    scalarCheck (table.cell ⟨129, by decide⟩) = true := by
  kernel_decide

theorem certificate_129 :
    Certificate (table.cell ⟨129, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_129,
    crossing_of_check crossingCheck_129,
    scalar_of_check scalarCheck_129⟩

end Erdos1038.HighKPlatformConstantTableChunk129
