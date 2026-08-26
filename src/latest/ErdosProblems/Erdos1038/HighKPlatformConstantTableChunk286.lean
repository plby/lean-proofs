import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 286 through 286. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk286

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_286 :
    geometryCheck (table.cell ⟨286, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_286 :
    crossingCheck (table.cell ⟨286, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_286 :
    scalarCheck (table.cell ⟨286, by decide⟩) = true := by
  kernel_decide

theorem certificate_286 :
    Certificate (table.cell ⟨286, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_286,
    crossing_of_check crossingCheck_286,
    scalar_of_check scalarCheck_286⟩

end Erdos1038.HighKPlatformConstantTableChunk286
