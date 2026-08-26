import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 491 through 491. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk491

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_491 :
    geometryCheck (table.cell ⟨491, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_491 :
    crossingCheck (table.cell ⟨491, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_491 :
    scalarCheck (table.cell ⟨491, by decide⟩) = true := by
  kernel_decide

theorem certificate_491 :
    Certificate (table.cell ⟨491, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_491,
    crossing_of_check crossingCheck_491,
    scalar_of_check scalarCheck_491⟩

end Erdos1038.HighKPlatformConstantTableChunk491
