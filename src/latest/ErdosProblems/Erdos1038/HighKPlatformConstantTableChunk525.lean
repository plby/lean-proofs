import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 525 through 525. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk525

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_525 :
    geometryCheck (table.cell ⟨525, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_525 :
    crossingCheck (table.cell ⟨525, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_525 :
    scalarCheck (table.cell ⟨525, by decide⟩) = true := by
  kernel_decide

theorem certificate_525 :
    Certificate (table.cell ⟨525, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_525,
    crossing_of_check crossingCheck_525,
    scalar_of_check scalarCheck_525⟩

end Erdos1038.HighKPlatformConstantTableChunk525
