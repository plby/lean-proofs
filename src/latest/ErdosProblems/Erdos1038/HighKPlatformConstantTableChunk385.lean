import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 385 through 385. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk385

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_385 :
    geometryCheck (table.cell ⟨385, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_385 :
    crossingCheck (table.cell ⟨385, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_385 :
    scalarCheck (table.cell ⟨385, by decide⟩) = true := by
  kernel_decide

theorem certificate_385 :
    Certificate (table.cell ⟨385, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_385,
    crossing_of_check crossingCheck_385,
    scalar_of_check scalarCheck_385⟩

end Erdos1038.HighKPlatformConstantTableChunk385
