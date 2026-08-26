import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 675 through 675. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk675

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_675 :
    geometryCheck (table.cell ⟨675, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_675 :
    crossingCheck (table.cell ⟨675, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_675 :
    scalarCheck (table.cell ⟨675, by decide⟩) = true := by
  kernel_decide

theorem certificate_675 :
    Certificate (table.cell ⟨675, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_675,
    crossing_of_check crossingCheck_675,
    scalar_of_check scalarCheck_675⟩

end Erdos1038.HighKPlatformConstantTableChunk675
