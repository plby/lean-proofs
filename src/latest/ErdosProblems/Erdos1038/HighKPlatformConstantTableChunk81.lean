import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 81 through 81. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk81

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_081 :
    geometryCheck (table.cell ⟨81, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_081 :
    crossingCheck (table.cell ⟨81, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_081 :
    scalarCheck (table.cell ⟨81, by decide⟩) = true := by
  kernel_decide

theorem certificate_081 :
    Certificate (table.cell ⟨81, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_081,
    crossing_of_check crossingCheck_081,
    scalar_of_check scalarCheck_081⟩

end Erdos1038.HighKPlatformConstantTableChunk81
