import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 522 through 522. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk522

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_522 :
    geometryCheck (table.cell ⟨522, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_522 :
    crossingCheck (table.cell ⟨522, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_522 :
    scalarCheck (table.cell ⟨522, by decide⟩) = true := by
  kernel_decide

theorem certificate_522 :
    Certificate (table.cell ⟨522, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_522,
    crossing_of_check crossingCheck_522,
    scalar_of_check scalarCheck_522⟩

end Erdos1038.HighKPlatformConstantTableChunk522
