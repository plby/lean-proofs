import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 249 through 249. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk249

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_249 :
    geometryCheck (table.cell ⟨249, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_249 :
    crossingCheck (table.cell ⟨249, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_249 :
    scalarCheck (table.cell ⟨249, by decide⟩) = true := by
  kernel_decide

theorem certificate_249 :
    Certificate (table.cell ⟨249, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_249,
    crossing_of_check crossingCheck_249,
    scalar_of_check scalarCheck_249⟩

end Erdos1038.HighKPlatformConstantTableChunk249
