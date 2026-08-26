import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 605 through 605. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk605

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_605 :
    geometryCheck (table.cell ⟨605, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_605 :
    crossingCheck (table.cell ⟨605, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_605 :
    scalarCheck (table.cell ⟨605, by decide⟩) = true := by
  kernel_decide

theorem certificate_605 :
    Certificate (table.cell ⟨605, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_605,
    crossing_of_check crossingCheck_605,
    scalar_of_check scalarCheck_605⟩

end Erdos1038.HighKPlatformConstantTableChunk605
