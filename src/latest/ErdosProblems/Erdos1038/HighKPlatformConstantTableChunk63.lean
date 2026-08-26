import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 63 through 63. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk63

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_063 :
    geometryCheck (table.cell ⟨63, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_063 :
    crossingCheck (table.cell ⟨63, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_063 :
    scalarCheck (table.cell ⟨63, by decide⟩) = true := by
  kernel_decide

theorem certificate_063 :
    Certificate (table.cell ⟨63, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_063,
    crossing_of_check crossingCheck_063,
    scalar_of_check scalarCheck_063⟩

end Erdos1038.HighKPlatformConstantTableChunk63
