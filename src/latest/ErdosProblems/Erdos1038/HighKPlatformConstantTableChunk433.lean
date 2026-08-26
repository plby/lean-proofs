import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 433 through 433. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk433

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_433 :
    geometryCheck (table.cell ⟨433, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_433 :
    crossingCheck (table.cell ⟨433, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_433 :
    scalarCheck (table.cell ⟨433, by decide⟩) = true := by
  kernel_decide

theorem certificate_433 :
    Certificate (table.cell ⟨433, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_433,
    crossing_of_check crossingCheck_433,
    scalar_of_check scalarCheck_433⟩

end Erdos1038.HighKPlatformConstantTableChunk433
