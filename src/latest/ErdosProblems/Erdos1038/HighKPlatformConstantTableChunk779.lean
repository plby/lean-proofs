import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 779 through 779. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk779

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_779 :
    geometryCheck (table.cell ⟨779, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_779 :
    crossingCheck (table.cell ⟨779, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_779 :
    scalarCheck (table.cell ⟨779, by decide⟩) = true := by
  kernel_decide

theorem certificate_779 :
    Certificate (table.cell ⟨779, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_779,
    crossing_of_check crossingCheck_779,
    scalar_of_check scalarCheck_779⟩

end Erdos1038.HighKPlatformConstantTableChunk779
