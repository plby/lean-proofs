import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 198 through 198. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk198

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_198 :
    geometryCheck (table.cell ⟨198, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_198 :
    crossingCheck (table.cell ⟨198, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_198 :
    scalarCheck (table.cell ⟨198, by decide⟩) = true := by
  kernel_decide

theorem certificate_198 :
    Certificate (table.cell ⟨198, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_198,
    crossing_of_check crossingCheck_198,
    scalar_of_check scalarCheck_198⟩

end Erdos1038.HighKPlatformConstantTableChunk198
