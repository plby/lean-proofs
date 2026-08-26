import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 204 through 204. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk204

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_204 :
    geometryCheck (table.cell ⟨204, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_204 :
    crossingCheck (table.cell ⟨204, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_204 :
    scalarCheck (table.cell ⟨204, by decide⟩) = true := by
  kernel_decide

theorem certificate_204 :
    Certificate (table.cell ⟨204, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_204,
    crossing_of_check crossingCheck_204,
    scalar_of_check scalarCheck_204⟩

end Erdos1038.HighKPlatformConstantTableChunk204
