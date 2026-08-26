import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 471 through 471. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk471

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_471 :
    geometryCheck (table.cell ⟨471, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_471 :
    crossingCheck (table.cell ⟨471, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_471 :
    scalarCheck (table.cell ⟨471, by decide⟩) = true := by
  kernel_decide

theorem certificate_471 :
    Certificate (table.cell ⟨471, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_471,
    crossing_of_check crossingCheck_471,
    scalar_of_check scalarCheck_471⟩

end Erdos1038.HighKPlatformConstantTableChunk471
