import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 542 through 542. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk542

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_542 :
    geometryCheck (table.cell ⟨542, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_542 :
    crossingCheck (table.cell ⟨542, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_542 :
    scalarCheck (table.cell ⟨542, by decide⟩) = true := by
  kernel_decide

theorem certificate_542 :
    Certificate (table.cell ⟨542, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_542,
    crossing_of_check crossingCheck_542,
    scalar_of_check scalarCheck_542⟩

end Erdos1038.HighKPlatformConstantTableChunk542
