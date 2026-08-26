import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 238 through 238. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk238

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_238 :
    geometryCheck (table.cell ⟨238, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_238 :
    crossingCheck (table.cell ⟨238, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_238 :
    scalarCheck (table.cell ⟨238, by decide⟩) = true := by
  kernel_decide

theorem certificate_238 :
    Certificate (table.cell ⟨238, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_238,
    crossing_of_check crossingCheck_238,
    scalar_of_check scalarCheck_238⟩

end Erdos1038.HighKPlatformConstantTableChunk238
