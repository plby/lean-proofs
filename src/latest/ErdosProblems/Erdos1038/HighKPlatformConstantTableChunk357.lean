import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 357 through 357. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk357

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_357 :
    geometryCheck (table.cell ⟨357, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_357 :
    crossingCheck (table.cell ⟨357, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_357 :
    scalarCheck (table.cell ⟨357, by decide⟩) = true := by
  kernel_decide

theorem certificate_357 :
    Certificate (table.cell ⟨357, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_357,
    crossing_of_check crossingCheck_357,
    scalar_of_check scalarCheck_357⟩

end Erdos1038.HighKPlatformConstantTableChunk357
