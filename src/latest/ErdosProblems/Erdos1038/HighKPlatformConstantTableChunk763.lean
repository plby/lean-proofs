import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 763 through 763. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk763

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_763 :
    geometryCheck (table.cell ⟨763, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_763 :
    crossingCheck (table.cell ⟨763, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_763 :
    scalarCheck (table.cell ⟨763, by decide⟩) = true := by
  kernel_decide

theorem certificate_763 :
    Certificate (table.cell ⟨763, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_763,
    crossing_of_check crossingCheck_763,
    scalar_of_check scalarCheck_763⟩

end Erdos1038.HighKPlatformConstantTableChunk763
