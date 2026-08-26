import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 146 through 146. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk146

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_146 :
    geometryCheck (table.cell ⟨146, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_146 :
    crossingCheck (table.cell ⟨146, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_146 :
    scalarCheck (table.cell ⟨146, by decide⟩) = true := by
  kernel_decide

theorem certificate_146 :
    Certificate (table.cell ⟨146, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_146,
    crossing_of_check crossingCheck_146,
    scalar_of_check scalarCheck_146⟩

end Erdos1038.HighKPlatformConstantTableChunk146
