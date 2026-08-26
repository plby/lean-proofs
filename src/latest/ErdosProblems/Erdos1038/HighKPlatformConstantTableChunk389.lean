import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 389 through 389. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk389

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_389 :
    geometryCheck (table.cell ⟨389, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_389 :
    crossingCheck (table.cell ⟨389, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_389 :
    scalarCheck (table.cell ⟨389, by decide⟩) = true := by
  kernel_decide

theorem certificate_389 :
    Certificate (table.cell ⟨389, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_389,
    crossing_of_check crossingCheck_389,
    scalar_of_check scalarCheck_389⟩

end Erdos1038.HighKPlatformConstantTableChunk389
