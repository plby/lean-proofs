import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 284 through 284. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk284

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_284 :
    geometryCheck (table.cell ⟨284, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_284 :
    crossingCheck (table.cell ⟨284, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_284 :
    scalarCheck (table.cell ⟨284, by decide⟩) = true := by
  kernel_decide

theorem certificate_284 :
    Certificate (table.cell ⟨284, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_284,
    crossing_of_check crossingCheck_284,
    scalar_of_check scalarCheck_284⟩

end Erdos1038.HighKPlatformConstantTableChunk284
