import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 376 through 376. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk376

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_376 :
    geometryCheck (table.cell ⟨376, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_376 :
    crossingCheck (table.cell ⟨376, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_376 :
    scalarCheck (table.cell ⟨376, by decide⟩) = true := by
  kernel_decide

theorem certificate_376 :
    Certificate (table.cell ⟨376, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_376,
    crossing_of_check crossingCheck_376,
    scalar_of_check scalarCheck_376⟩

end Erdos1038.HighKPlatformConstantTableChunk376
