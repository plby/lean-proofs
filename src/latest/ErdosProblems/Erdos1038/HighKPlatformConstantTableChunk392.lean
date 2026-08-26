import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 392 through 392. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk392

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_392 :
    geometryCheck (table.cell ⟨392, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_392 :
    crossingCheck (table.cell ⟨392, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_392 :
    scalarCheck (table.cell ⟨392, by decide⟩) = true := by
  kernel_decide

theorem certificate_392 :
    Certificate (table.cell ⟨392, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_392,
    crossing_of_check crossingCheck_392,
    scalar_of_check scalarCheck_392⟩

end Erdos1038.HighKPlatformConstantTableChunk392
