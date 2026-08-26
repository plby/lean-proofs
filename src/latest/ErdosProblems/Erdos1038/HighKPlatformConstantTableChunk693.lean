import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 693 through 693. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk693

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_693 :
    geometryCheck (table.cell ⟨693, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_693 :
    crossingCheck (table.cell ⟨693, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_693 :
    scalarCheck (table.cell ⟨693, by decide⟩) = true := by
  kernel_decide

theorem certificate_693 :
    Certificate (table.cell ⟨693, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_693,
    crossing_of_check crossingCheck_693,
    scalar_of_check scalarCheck_693⟩

end Erdos1038.HighKPlatformConstantTableChunk693
