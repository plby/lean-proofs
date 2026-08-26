import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 71 through 71. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk71

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_071 :
    geometryCheck (table.cell ⟨71, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_071 :
    crossingCheck (table.cell ⟨71, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_071 :
    scalarCheck (table.cell ⟨71, by decide⟩) = true := by
  kernel_decide

theorem certificate_071 :
    Certificate (table.cell ⟨71, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_071,
    crossing_of_check crossingCheck_071,
    scalar_of_check scalarCheck_071⟩

end Erdos1038.HighKPlatformConstantTableChunk71
