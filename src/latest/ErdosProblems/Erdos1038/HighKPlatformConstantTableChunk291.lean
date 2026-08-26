import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 291 through 291. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk291

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_291 :
    geometryCheck (table.cell ⟨291, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_291 :
    crossingCheck (table.cell ⟨291, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_291 :
    scalarCheck (table.cell ⟨291, by decide⟩) = true := by
  kernel_decide

theorem certificate_291 :
    Certificate (table.cell ⟨291, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_291,
    crossing_of_check crossingCheck_291,
    scalar_of_check scalarCheck_291⟩

end Erdos1038.HighKPlatformConstantTableChunk291
