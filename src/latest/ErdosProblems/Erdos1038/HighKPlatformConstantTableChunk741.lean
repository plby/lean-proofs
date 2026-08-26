import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 741 through 741. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk741

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_741 :
    geometryCheck (table.cell ⟨741, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_741 :
    crossingCheck (table.cell ⟨741, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_741 :
    scalarCheck (table.cell ⟨741, by decide⟩) = true := by
  kernel_decide

theorem certificate_741 :
    Certificate (table.cell ⟨741, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_741,
    crossing_of_check crossingCheck_741,
    scalar_of_check scalarCheck_741⟩

end Erdos1038.HighKPlatformConstantTableChunk741
