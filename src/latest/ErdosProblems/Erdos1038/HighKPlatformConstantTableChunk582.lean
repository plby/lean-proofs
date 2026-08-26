import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 582 through 582. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk582

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_582 :
    geometryCheck (table.cell ⟨582, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_582 :
    crossingCheck (table.cell ⟨582, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_582 :
    scalarCheck (table.cell ⟨582, by decide⟩) = true := by
  kernel_decide

theorem certificate_582 :
    Certificate (table.cell ⟨582, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_582,
    crossing_of_check crossingCheck_582,
    scalar_of_check scalarCheck_582⟩

end Erdos1038.HighKPlatformConstantTableChunk582
