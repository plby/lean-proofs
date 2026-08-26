import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 428 through 428. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk428

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_428 :
    geometryCheck (table.cell ⟨428, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_428 :
    crossingCheck (table.cell ⟨428, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_428 :
    scalarCheck (table.cell ⟨428, by decide⟩) = true := by
  kernel_decide

theorem certificate_428 :
    Certificate (table.cell ⟨428, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_428,
    crossing_of_check crossingCheck_428,
    scalar_of_check scalarCheck_428⟩

end Erdos1038.HighKPlatformConstantTableChunk428
