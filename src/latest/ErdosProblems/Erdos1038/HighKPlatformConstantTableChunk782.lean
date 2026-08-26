import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 782 through 782. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk782

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_782 :
    geometryCheck (table.cell ⟨782, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_782 :
    crossingCheck (table.cell ⟨782, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_782 :
    scalarCheck (table.cell ⟨782, by decide⟩) = true := by
  kernel_decide

theorem certificate_782 :
    Certificate (table.cell ⟨782, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_782,
    crossing_of_check crossingCheck_782,
    scalar_of_check scalarCheck_782⟩

end Erdos1038.HighKPlatformConstantTableChunk782
