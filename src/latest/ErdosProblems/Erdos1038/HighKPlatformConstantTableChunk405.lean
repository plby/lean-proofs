import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 405 through 405. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk405

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_405 :
    geometryCheck (table.cell ⟨405, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_405 :
    crossingCheck (table.cell ⟨405, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_405 :
    scalarCheck (table.cell ⟨405, by decide⟩) = true := by
  kernel_decide

theorem certificate_405 :
    Certificate (table.cell ⟨405, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_405,
    crossing_of_check crossingCheck_405,
    scalar_of_check scalarCheck_405⟩

end Erdos1038.HighKPlatformConstantTableChunk405
