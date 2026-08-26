import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 473 through 473. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk473

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_473 :
    geometryCheck (table.cell ⟨473, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_473 :
    crossingCheck (table.cell ⟨473, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_473 :
    scalarCheck (table.cell ⟨473, by decide⟩) = true := by
  kernel_decide

theorem certificate_473 :
    Certificate (table.cell ⟨473, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_473,
    crossing_of_check crossingCheck_473,
    scalar_of_check scalarCheck_473⟩

end Erdos1038.HighKPlatformConstantTableChunk473
