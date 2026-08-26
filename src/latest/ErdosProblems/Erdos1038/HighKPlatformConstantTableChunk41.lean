import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 41 through 41. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk41

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_041 :
    geometryCheck (table.cell ⟨41, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_041 :
    crossingCheck (table.cell ⟨41, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_041 :
    scalarCheck (table.cell ⟨41, by decide⟩) = true := by
  kernel_decide

theorem certificate_041 :
    Certificate (table.cell ⟨41, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_041,
    crossing_of_check crossingCheck_041,
    scalar_of_check scalarCheck_041⟩

end Erdos1038.HighKPlatformConstantTableChunk41
