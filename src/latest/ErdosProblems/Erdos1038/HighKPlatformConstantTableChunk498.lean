import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 498 through 498. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk498

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_498 :
    geometryCheck (table.cell ⟨498, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_498 :
    crossingCheck (table.cell ⟨498, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_498 :
    scalarCheck (table.cell ⟨498, by decide⟩) = true := by
  kernel_decide

theorem certificate_498 :
    Certificate (table.cell ⟨498, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_498,
    crossing_of_check crossingCheck_498,
    scalar_of_check scalarCheck_498⟩

end Erdos1038.HighKPlatformConstantTableChunk498
