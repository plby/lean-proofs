import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 179 through 179. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk179

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_179 :
    geometryCheck (table.cell ⟨179, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_179 :
    crossingCheck (table.cell ⟨179, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_179 :
    scalarCheck (table.cell ⟨179, by decide⟩) = true := by
  kernel_decide

theorem certificate_179 :
    Certificate (table.cell ⟨179, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_179,
    crossing_of_check crossingCheck_179,
    scalar_of_check scalarCheck_179⟩

end Erdos1038.HighKPlatformConstantTableChunk179
