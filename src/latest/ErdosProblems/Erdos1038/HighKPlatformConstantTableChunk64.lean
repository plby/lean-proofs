import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 64 through 64. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk64

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_064 :
    geometryCheck (table.cell ⟨64, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_064 :
    crossingCheck (table.cell ⟨64, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_064 :
    scalarCheck (table.cell ⟨64, by decide⟩) = true := by
  kernel_decide

theorem certificate_064 :
    Certificate (table.cell ⟨64, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_064,
    crossing_of_check crossingCheck_064,
    scalar_of_check scalarCheck_064⟩

end Erdos1038.HighKPlatformConstantTableChunk64
