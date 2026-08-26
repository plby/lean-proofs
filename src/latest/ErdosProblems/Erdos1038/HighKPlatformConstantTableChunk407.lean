import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 407 through 407. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk407

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_407 :
    geometryCheck (table.cell ⟨407, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_407 :
    crossingCheck (table.cell ⟨407, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_407 :
    scalarCheck (table.cell ⟨407, by decide⟩) = true := by
  kernel_decide

theorem certificate_407 :
    Certificate (table.cell ⟨407, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_407,
    crossing_of_check crossingCheck_407,
    scalar_of_check scalarCheck_407⟩

end Erdos1038.HighKPlatformConstantTableChunk407
