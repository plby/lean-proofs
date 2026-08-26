import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 396 through 396. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk396

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_396 :
    geometryCheck (table.cell ⟨396, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_396 :
    crossingCheck (table.cell ⟨396, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_396 :
    scalarCheck (table.cell ⟨396, by decide⟩) = true := by
  kernel_decide

theorem certificate_396 :
    Certificate (table.cell ⟨396, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_396,
    crossing_of_check crossingCheck_396,
    scalar_of_check scalarCheck_396⟩

end Erdos1038.HighKPlatformConstantTableChunk396
