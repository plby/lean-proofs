import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 635 through 635. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk635

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_635 :
    geometryCheck (table.cell ⟨635, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_635 :
    crossingCheck (table.cell ⟨635, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_635 :
    scalarCheck (table.cell ⟨635, by decide⟩) = true := by
  kernel_decide

theorem certificate_635 :
    Certificate (table.cell ⟨635, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_635,
    crossing_of_check crossingCheck_635,
    scalar_of_check scalarCheck_635⟩

end Erdos1038.HighKPlatformConstantTableChunk635
