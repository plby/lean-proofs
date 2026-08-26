import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 260 through 260. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk260

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_260 :
    geometryCheck (table.cell ⟨260, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_260 :
    crossingCheck (table.cell ⟨260, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_260 :
    scalarCheck (table.cell ⟨260, by decide⟩) = true := by
  kernel_decide

theorem certificate_260 :
    Certificate (table.cell ⟨260, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_260,
    crossing_of_check crossingCheck_260,
    scalar_of_check scalarCheck_260⟩

end Erdos1038.HighKPlatformConstantTableChunk260
