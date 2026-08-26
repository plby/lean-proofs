import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 378 through 378. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk378

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_378 :
    geometryCheck (table.cell ⟨378, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_378 :
    crossingCheck (table.cell ⟨378, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_378 :
    scalarCheck (table.cell ⟨378, by decide⟩) = true := by
  kernel_decide

theorem certificate_378 :
    Certificate (table.cell ⟨378, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_378,
    crossing_of_check crossingCheck_378,
    scalar_of_check scalarCheck_378⟩

end Erdos1038.HighKPlatformConstantTableChunk378
