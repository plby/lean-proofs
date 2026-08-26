import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 815 through 815. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk815

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_815 :
    geometryCheck (table.cell ⟨815, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_815 :
    crossingCheck (table.cell ⟨815, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_815 :
    scalarCheck (table.cell ⟨815, by decide⟩) = true := by
  kernel_decide

theorem certificate_815 :
    Certificate (table.cell ⟨815, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_815,
    crossing_of_check crossingCheck_815,
    scalar_of_check scalarCheck_815⟩

end Erdos1038.HighKPlatformConstantTableChunk815
