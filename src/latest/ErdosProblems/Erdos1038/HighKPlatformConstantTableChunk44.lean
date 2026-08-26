import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 44 through 44. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk44

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_044 :
    geometryCheck (table.cell ⟨44, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_044 :
    crossingCheck (table.cell ⟨44, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_044 :
    scalarCheck (table.cell ⟨44, by decide⟩) = true := by
  kernel_decide

theorem certificate_044 :
    Certificate (table.cell ⟨44, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_044,
    crossing_of_check crossingCheck_044,
    scalar_of_check scalarCheck_044⟩

end Erdos1038.HighKPlatformConstantTableChunk44
