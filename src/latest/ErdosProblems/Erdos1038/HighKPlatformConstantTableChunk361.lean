import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 361 through 361. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk361

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_361 :
    geometryCheck (table.cell ⟨361, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_361 :
    crossingCheck (table.cell ⟨361, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_361 :
    scalarCheck (table.cell ⟨361, by decide⟩) = true := by
  kernel_decide

theorem certificate_361 :
    Certificate (table.cell ⟨361, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_361,
    crossing_of_check crossingCheck_361,
    scalar_of_check scalarCheck_361⟩

end Erdos1038.HighKPlatformConstantTableChunk361
