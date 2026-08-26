import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 526 through 526. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk526

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_526 :
    geometryCheck (table.cell ⟨526, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_526 :
    crossingCheck (table.cell ⟨526, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_526 :
    scalarCheck (table.cell ⟨526, by decide⟩) = true := by
  kernel_decide

theorem certificate_526 :
    Certificate (table.cell ⟨526, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_526,
    crossing_of_check crossingCheck_526,
    scalar_of_check scalarCheck_526⟩

end Erdos1038.HighKPlatformConstantTableChunk526
