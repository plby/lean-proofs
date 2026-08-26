import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 476 through 476. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk476

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_476 :
    geometryCheck (table.cell ⟨476, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_476 :
    crossingCheck (table.cell ⟨476, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_476 :
    scalarCheck (table.cell ⟨476, by decide⟩) = true := by
  kernel_decide

theorem certificate_476 :
    Certificate (table.cell ⟨476, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_476,
    crossing_of_check crossingCheck_476,
    scalar_of_check scalarCheck_476⟩

end Erdos1038.HighKPlatformConstantTableChunk476
