import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 178 through 178. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk178

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_178 :
    geometryCheck (table.cell ⟨178, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_178 :
    crossingCheck (table.cell ⟨178, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_178 :
    scalarCheck (table.cell ⟨178, by decide⟩) = true := by
  kernel_decide

theorem certificate_178 :
    Certificate (table.cell ⟨178, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_178,
    crossing_of_check crossingCheck_178,
    scalar_of_check scalarCheck_178⟩

end Erdos1038.HighKPlatformConstantTableChunk178
