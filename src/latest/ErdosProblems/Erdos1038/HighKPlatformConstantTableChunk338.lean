import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 338 through 338. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk338

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_338 :
    geometryCheck (table.cell ⟨338, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_338 :
    crossingCheck (table.cell ⟨338, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_338 :
    scalarCheck (table.cell ⟨338, by decide⟩) = true := by
  kernel_decide

theorem certificate_338 :
    Certificate (table.cell ⟨338, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_338,
    crossing_of_check crossingCheck_338,
    scalar_of_check scalarCheck_338⟩

end Erdos1038.HighKPlatformConstantTableChunk338
