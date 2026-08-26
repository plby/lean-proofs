import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 236 through 236. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk236

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_236 :
    geometryCheck (table.cell ⟨236, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_236 :
    crossingCheck (table.cell ⟨236, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_236 :
    scalarCheck (table.cell ⟨236, by decide⟩) = true := by
  kernel_decide

theorem certificate_236 :
    Certificate (table.cell ⟨236, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_236,
    crossing_of_check crossingCheck_236,
    scalar_of_check scalarCheck_236⟩

end Erdos1038.HighKPlatformConstantTableChunk236
