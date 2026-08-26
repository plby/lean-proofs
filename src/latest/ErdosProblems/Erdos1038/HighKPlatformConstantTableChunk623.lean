import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 623 through 623. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk623

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_623 :
    geometryCheck (table.cell ⟨623, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_623 :
    crossingCheck (table.cell ⟨623, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_623 :
    scalarCheck (table.cell ⟨623, by decide⟩) = true := by
  kernel_decide

theorem certificate_623 :
    Certificate (table.cell ⟨623, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_623,
    crossing_of_check crossingCheck_623,
    scalar_of_check scalarCheck_623⟩

end Erdos1038.HighKPlatformConstantTableChunk623
