import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 460 through 460. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk460

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_460 :
    geometryCheck (table.cell ⟨460, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_460 :
    crossingCheck (table.cell ⟨460, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_460 :
    scalarCheck (table.cell ⟨460, by decide⟩) = true := by
  kernel_decide

theorem certificate_460 :
    Certificate (table.cell ⟨460, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_460,
    crossing_of_check crossingCheck_460,
    scalar_of_check scalarCheck_460⟩

end Erdos1038.HighKPlatformConstantTableChunk460
