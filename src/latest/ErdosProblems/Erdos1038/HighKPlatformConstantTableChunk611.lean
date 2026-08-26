import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 611 through 611. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk611

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_611 :
    geometryCheck (table.cell ⟨611, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_611 :
    crossingCheck (table.cell ⟨611, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_611 :
    scalarCheck (table.cell ⟨611, by decide⟩) = true := by
  kernel_decide

theorem certificate_611 :
    Certificate (table.cell ⟨611, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_611,
    crossing_of_check crossingCheck_611,
    scalar_of_check scalarCheck_611⟩

end Erdos1038.HighKPlatformConstantTableChunk611
