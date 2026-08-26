import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 595 through 595. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk595

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_595 :
    geometryCheck (table.cell ⟨595, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_595 :
    crossingCheck (table.cell ⟨595, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_595 :
    scalarCheck (table.cell ⟨595, by decide⟩) = true := by
  kernel_decide

theorem certificate_595 :
    Certificate (table.cell ⟨595, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_595,
    crossing_of_check crossingCheck_595,
    scalar_of_check scalarCheck_595⟩

end Erdos1038.HighKPlatformConstantTableChunk595
