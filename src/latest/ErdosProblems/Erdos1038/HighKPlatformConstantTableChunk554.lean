import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 554 through 554. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk554

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_554 :
    geometryCheck (table.cell ⟨554, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_554 :
    crossingCheck (table.cell ⟨554, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_554 :
    scalarCheck (table.cell ⟨554, by decide⟩) = true := by
  kernel_decide

theorem certificate_554 :
    Certificate (table.cell ⟨554, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_554,
    crossing_of_check crossingCheck_554,
    scalar_of_check scalarCheck_554⟩

end Erdos1038.HighKPlatformConstantTableChunk554
