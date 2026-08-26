import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 413 through 413. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk413

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_413 :
    geometryCheck (table.cell ⟨413, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_413 :
    crossingCheck (table.cell ⟨413, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_413 :
    scalarCheck (table.cell ⟨413, by decide⟩) = true := by
  kernel_decide

theorem certificate_413 :
    Certificate (table.cell ⟨413, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_413,
    crossing_of_check crossingCheck_413,
    scalar_of_check scalarCheck_413⟩

end Erdos1038.HighKPlatformConstantTableChunk413
