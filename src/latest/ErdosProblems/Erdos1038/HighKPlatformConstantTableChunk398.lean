import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 398 through 398. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk398

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_398 :
    geometryCheck (table.cell ⟨398, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_398 :
    crossingCheck (table.cell ⟨398, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_398 :
    scalarCheck (table.cell ⟨398, by decide⟩) = true := by
  kernel_decide

theorem certificate_398 :
    Certificate (table.cell ⟨398, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_398,
    crossing_of_check crossingCheck_398,
    scalar_of_check scalarCheck_398⟩

end Erdos1038.HighKPlatformConstantTableChunk398
