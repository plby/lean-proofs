import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 314 through 314. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk314

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_314 :
    geometryCheck (table.cell ⟨314, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_314 :
    crossingCheck (table.cell ⟨314, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_314 :
    scalarCheck (table.cell ⟨314, by decide⟩) = true := by
  kernel_decide

theorem certificate_314 :
    Certificate (table.cell ⟨314, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_314,
    crossing_of_check crossingCheck_314,
    scalar_of_check scalarCheck_314⟩

end Erdos1038.HighKPlatformConstantTableChunk314
