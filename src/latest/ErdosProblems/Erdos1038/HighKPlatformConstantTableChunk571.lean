import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 571 through 571. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk571

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_571 :
    geometryCheck (table.cell ⟨571, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_571 :
    crossingCheck (table.cell ⟨571, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_571 :
    scalarCheck (table.cell ⟨571, by decide⟩) = true := by
  kernel_decide

theorem certificate_571 :
    Certificate (table.cell ⟨571, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_571,
    crossing_of_check crossingCheck_571,
    scalar_of_check scalarCheck_571⟩

end Erdos1038.HighKPlatformConstantTableChunk571
