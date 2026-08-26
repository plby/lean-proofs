import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 438 through 438. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk438

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_438 :
    geometryCheck (table.cell ⟨438, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_438 :
    crossingCheck (table.cell ⟨438, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_438 :
    scalarCheck (table.cell ⟨438, by decide⟩) = true := by
  kernel_decide

theorem certificate_438 :
    Certificate (table.cell ⟨438, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_438,
    crossing_of_check crossingCheck_438,
    scalar_of_check scalarCheck_438⟩

end Erdos1038.HighKPlatformConstantTableChunk438
