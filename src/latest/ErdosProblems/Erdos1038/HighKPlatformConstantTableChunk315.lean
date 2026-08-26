import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 315 through 315. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk315

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_315 :
    geometryCheck (table.cell ⟨315, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_315 :
    crossingCheck (table.cell ⟨315, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_315 :
    scalarCheck (table.cell ⟨315, by decide⟩) = true := by
  kernel_decide

theorem certificate_315 :
    Certificate (table.cell ⟨315, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_315,
    crossing_of_check crossingCheck_315,
    scalar_of_check scalarCheck_315⟩

end Erdos1038.HighKPlatformConstantTableChunk315
