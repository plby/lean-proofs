import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 283 through 283. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk283

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_283 :
    geometryCheck (table.cell ⟨283, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_283 :
    crossingCheck (table.cell ⟨283, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_283 :
    scalarCheck (table.cell ⟨283, by decide⟩) = true := by
  kernel_decide

theorem certificate_283 :
    Certificate (table.cell ⟨283, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_283,
    crossing_of_check crossingCheck_283,
    scalar_of_check scalarCheck_283⟩

end Erdos1038.HighKPlatformConstantTableChunk283
