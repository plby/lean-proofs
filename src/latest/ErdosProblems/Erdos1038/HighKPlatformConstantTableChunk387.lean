import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 387 through 387. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk387

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_387 :
    geometryCheck (table.cell ⟨387, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_387 :
    crossingCheck (table.cell ⟨387, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_387 :
    scalarCheck (table.cell ⟨387, by decide⟩) = true := by
  kernel_decide

theorem certificate_387 :
    Certificate (table.cell ⟨387, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_387,
    crossing_of_check crossingCheck_387,
    scalar_of_check scalarCheck_387⟩

end Erdos1038.HighKPlatformConstantTableChunk387
