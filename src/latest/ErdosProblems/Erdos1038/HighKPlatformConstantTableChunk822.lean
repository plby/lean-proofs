import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 822 through 822. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk822

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_822 :
    geometryCheck (table.cell ⟨822, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_822 :
    crossingCheck (table.cell ⟨822, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_822 :
    scalarCheck (table.cell ⟨822, by decide⟩) = true := by
  kernel_decide

theorem certificate_822 :
    Certificate (table.cell ⟨822, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_822,
    crossing_of_check crossingCheck_822,
    scalar_of_check scalarCheck_822⟩

end Erdos1038.HighKPlatformConstantTableChunk822
