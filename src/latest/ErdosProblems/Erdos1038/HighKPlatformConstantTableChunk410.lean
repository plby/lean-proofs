import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 410 through 410. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk410

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_410 :
    geometryCheck (table.cell ⟨410, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_410 :
    crossingCheck (table.cell ⟨410, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_410 :
    scalarCheck (table.cell ⟨410, by decide⟩) = true := by
  kernel_decide

theorem certificate_410 :
    Certificate (table.cell ⟨410, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_410,
    crossing_of_check crossingCheck_410,
    scalar_of_check scalarCheck_410⟩

end Erdos1038.HighKPlatformConstantTableChunk410
