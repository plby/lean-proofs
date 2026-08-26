import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 533 through 533. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk533

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_533 :
    geometryCheck (table.cell ⟨533, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_533 :
    crossingCheck (table.cell ⟨533, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_533 :
    scalarCheck (table.cell ⟨533, by decide⟩) = true := by
  kernel_decide

theorem certificate_533 :
    Certificate (table.cell ⟨533, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_533,
    crossing_of_check crossingCheck_533,
    scalar_of_check scalarCheck_533⟩

end Erdos1038.HighKPlatformConstantTableChunk533
