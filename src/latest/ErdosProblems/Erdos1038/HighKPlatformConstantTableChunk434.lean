import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 434 through 434. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk434

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_434 :
    geometryCheck (table.cell ⟨434, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_434 :
    crossingCheck (table.cell ⟨434, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_434 :
    scalarCheck (table.cell ⟨434, by decide⟩) = true := by
  kernel_decide

theorem certificate_434 :
    Certificate (table.cell ⟨434, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_434,
    crossing_of_check crossingCheck_434,
    scalar_of_check scalarCheck_434⟩

end Erdos1038.HighKPlatformConstantTableChunk434
