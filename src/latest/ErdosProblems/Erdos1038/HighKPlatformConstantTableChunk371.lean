import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 371 through 371. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk371

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_371 :
    geometryCheck (table.cell ⟨371, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_371 :
    crossingCheck (table.cell ⟨371, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_371 :
    scalarCheck (table.cell ⟨371, by decide⟩) = true := by
  kernel_decide

theorem certificate_371 :
    Certificate (table.cell ⟨371, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_371,
    crossing_of_check crossingCheck_371,
    scalar_of_check scalarCheck_371⟩

end Erdos1038.HighKPlatformConstantTableChunk371
