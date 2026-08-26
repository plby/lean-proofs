import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 545 through 545. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk545

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_545 :
    geometryCheck (table.cell ⟨545, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_545 :
    crossingCheck (table.cell ⟨545, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_545 :
    scalarCheck (table.cell ⟨545, by decide⟩) = true := by
  kernel_decide

theorem certificate_545 :
    Certificate (table.cell ⟨545, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_545,
    crossing_of_check crossingCheck_545,
    scalar_of_check scalarCheck_545⟩

end Erdos1038.HighKPlatformConstantTableChunk545
