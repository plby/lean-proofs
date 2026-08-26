import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 748 through 748. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk748

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_748 :
    geometryCheck (table.cell ⟨748, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_748 :
    crossingCheck (table.cell ⟨748, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_748 :
    scalarCheck (table.cell ⟨748, by decide⟩) = true := by
  kernel_decide

theorem certificate_748 :
    Certificate (table.cell ⟨748, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_748,
    crossing_of_check crossingCheck_748,
    scalar_of_check scalarCheck_748⟩

end Erdos1038.HighKPlatformConstantTableChunk748
