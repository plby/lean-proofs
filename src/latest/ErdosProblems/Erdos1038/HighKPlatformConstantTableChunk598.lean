import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 598 through 598. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk598

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_598 :
    geometryCheck (table.cell ⟨598, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_598 :
    crossingCheck (table.cell ⟨598, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_598 :
    scalarCheck (table.cell ⟨598, by decide⟩) = true := by
  kernel_decide

theorem certificate_598 :
    Certificate (table.cell ⟨598, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_598,
    crossing_of_check crossingCheck_598,
    scalar_of_check scalarCheck_598⟩

end Erdos1038.HighKPlatformConstantTableChunk598
