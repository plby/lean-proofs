import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 270 through 270. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk270

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_270 :
    geometryCheck (table.cell ⟨270, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_270 :
    crossingCheck (table.cell ⟨270, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_270 :
    scalarCheck (table.cell ⟨270, by decide⟩) = true := by
  kernel_decide

theorem certificate_270 :
    Certificate (table.cell ⟨270, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_270,
    crossing_of_check crossingCheck_270,
    scalar_of_check scalarCheck_270⟩

end Erdos1038.HighKPlatformConstantTableChunk270
