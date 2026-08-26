import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 578 through 578. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk578

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_578 :
    geometryCheck (table.cell ⟨578, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_578 :
    crossingCheck (table.cell ⟨578, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_578 :
    scalarCheck (table.cell ⟨578, by decide⟩) = true := by
  kernel_decide

theorem certificate_578 :
    Certificate (table.cell ⟨578, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_578,
    crossing_of_check crossingCheck_578,
    scalar_of_check scalarCheck_578⟩

end Erdos1038.HighKPlatformConstantTableChunk578
