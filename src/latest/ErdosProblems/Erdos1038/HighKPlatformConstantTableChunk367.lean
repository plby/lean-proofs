import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 367 through 367. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk367

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_367 :
    geometryCheck (table.cell ⟨367, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_367 :
    crossingCheck (table.cell ⟨367, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_367 :
    scalarCheck (table.cell ⟨367, by decide⟩) = true := by
  kernel_decide

theorem certificate_367 :
    Certificate (table.cell ⟨367, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_367,
    crossing_of_check crossingCheck_367,
    scalar_of_check scalarCheck_367⟩

end Erdos1038.HighKPlatformConstantTableChunk367
