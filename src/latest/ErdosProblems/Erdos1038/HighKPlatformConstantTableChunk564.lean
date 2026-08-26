import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 564 through 564. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk564

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_564 :
    geometryCheck (table.cell ⟨564, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_564 :
    crossingCheck (table.cell ⟨564, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_564 :
    scalarCheck (table.cell ⟨564, by decide⟩) = true := by
  kernel_decide

theorem certificate_564 :
    Certificate (table.cell ⟨564, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_564,
    crossing_of_check crossingCheck_564,
    scalar_of_check scalarCheck_564⟩

end Erdos1038.HighKPlatformConstantTableChunk564
