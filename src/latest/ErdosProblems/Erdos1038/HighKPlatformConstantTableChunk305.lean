import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 305 through 305. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk305

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_305 :
    geometryCheck (table.cell ⟨305, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_305 :
    crossingCheck (table.cell ⟨305, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_305 :
    scalarCheck (table.cell ⟨305, by decide⟩) = true := by
  kernel_decide

theorem certificate_305 :
    Certificate (table.cell ⟨305, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_305,
    crossing_of_check crossingCheck_305,
    scalar_of_check scalarCheck_305⟩

end Erdos1038.HighKPlatformConstantTableChunk305
