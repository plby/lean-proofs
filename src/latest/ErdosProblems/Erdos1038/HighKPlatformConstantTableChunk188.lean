import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 188 through 188. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk188

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_188 :
    geometryCheck (table.cell ⟨188, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_188 :
    crossingCheck (table.cell ⟨188, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_188 :
    scalarCheck (table.cell ⟨188, by decide⟩) = true := by
  kernel_decide

theorem certificate_188 :
    Certificate (table.cell ⟨188, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_188,
    crossing_of_check crossingCheck_188,
    scalar_of_check scalarCheck_188⟩

end Erdos1038.HighKPlatformConstantTableChunk188
