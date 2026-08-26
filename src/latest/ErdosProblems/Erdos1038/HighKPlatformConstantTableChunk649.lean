import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 649 through 649. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk649

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_649 :
    geometryCheck (table.cell ⟨649, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_649 :
    crossingCheck (table.cell ⟨649, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_649 :
    scalarCheck (table.cell ⟨649, by decide⟩) = true := by
  kernel_decide

theorem certificate_649 :
    Certificate (table.cell ⟨649, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_649,
    crossing_of_check crossingCheck_649,
    scalar_of_check scalarCheck_649⟩

end Erdos1038.HighKPlatformConstantTableChunk649
