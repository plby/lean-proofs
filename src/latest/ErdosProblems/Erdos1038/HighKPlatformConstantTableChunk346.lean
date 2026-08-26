import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 346 through 346. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk346

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_346 :
    geometryCheck (table.cell ⟨346, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_346 :
    crossingCheck (table.cell ⟨346, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_346 :
    scalarCheck (table.cell ⟨346, by decide⟩) = true := by
  kernel_decide

theorem certificate_346 :
    Certificate (table.cell ⟨346, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_346,
    crossing_of_check crossingCheck_346,
    scalar_of_check scalarCheck_346⟩

end Erdos1038.HighKPlatformConstantTableChunk346
