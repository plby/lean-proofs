import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 639 through 639. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk639

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_639 :
    geometryCheck (table.cell ⟨639, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_639 :
    crossingCheck (table.cell ⟨639, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_639 :
    scalarCheck (table.cell ⟨639, by decide⟩) = true := by
  kernel_decide

theorem certificate_639 :
    Certificate (table.cell ⟨639, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_639,
    crossing_of_check crossingCheck_639,
    scalar_of_check scalarCheck_639⟩

end Erdos1038.HighKPlatformConstantTableChunk639
