import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 379 through 379. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk379

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_379 :
    geometryCheck (table.cell ⟨379, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_379 :
    crossingCheck (table.cell ⟨379, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_379 :
    scalarCheck (table.cell ⟨379, by decide⟩) = true := by
  kernel_decide

theorem certificate_379 :
    Certificate (table.cell ⟨379, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_379,
    crossing_of_check crossingCheck_379,
    scalar_of_check scalarCheck_379⟩

end Erdos1038.HighKPlatformConstantTableChunk379
