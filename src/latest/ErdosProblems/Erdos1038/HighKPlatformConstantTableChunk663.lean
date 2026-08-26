import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 663 through 663. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk663

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_663 :
    geometryCheck (table.cell ⟨663, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_663 :
    crossingCheck (table.cell ⟨663, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_663 :
    scalarCheck (table.cell ⟨663, by decide⟩) = true := by
  kernel_decide

theorem certificate_663 :
    Certificate (table.cell ⟨663, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_663,
    crossing_of_check crossingCheck_663,
    scalar_of_check scalarCheck_663⟩

end Erdos1038.HighKPlatformConstantTableChunk663
