import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 172 through 172. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk172

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_172 :
    geometryCheck (table.cell ⟨172, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_172 :
    crossingCheck (table.cell ⟨172, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_172 :
    scalarCheck (table.cell ⟨172, by decide⟩) = true := by
  kernel_decide

theorem certificate_172 :
    Certificate (table.cell ⟨172, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_172,
    crossing_of_check crossingCheck_172,
    scalar_of_check scalarCheck_172⟩

end Erdos1038.HighKPlatformConstantTableChunk172
