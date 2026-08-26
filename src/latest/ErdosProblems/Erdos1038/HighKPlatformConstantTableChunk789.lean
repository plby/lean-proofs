import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 789 through 789. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk789

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_789 :
    geometryCheck (table.cell ⟨789, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_789 :
    crossingCheck (table.cell ⟨789, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_789 :
    scalarCheck (table.cell ⟨789, by decide⟩) = true := by
  kernel_decide

theorem certificate_789 :
    Certificate (table.cell ⟨789, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_789,
    crossing_of_check crossingCheck_789,
    scalar_of_check scalarCheck_789⟩

end Erdos1038.HighKPlatformConstantTableChunk789
