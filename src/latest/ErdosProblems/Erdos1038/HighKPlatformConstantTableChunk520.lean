import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 520 through 520. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk520

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_520 :
    geometryCheck (table.cell ⟨520, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_520 :
    crossingCheck (table.cell ⟨520, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_520 :
    scalarCheck (table.cell ⟨520, by decide⟩) = true := by
  kernel_decide

theorem certificate_520 :
    Certificate (table.cell ⟨520, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_520,
    crossing_of_check crossingCheck_520,
    scalar_of_check scalarCheck_520⟩

end Erdos1038.HighKPlatformConstantTableChunk520
