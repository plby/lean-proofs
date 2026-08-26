import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 362 through 362. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk362

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_362 :
    geometryCheck (table.cell ⟨362, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_362 :
    crossingCheck (table.cell ⟨362, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_362 :
    scalarCheck (table.cell ⟨362, by decide⟩) = true := by
  kernel_decide

theorem certificate_362 :
    Certificate (table.cell ⟨362, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_362,
    crossing_of_check crossingCheck_362,
    scalar_of_check scalarCheck_362⟩

end Erdos1038.HighKPlatformConstantTableChunk362
