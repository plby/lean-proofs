import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 382 through 382. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk382

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_382 :
    geometryCheck (table.cell ⟨382, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_382 :
    crossingCheck (table.cell ⟨382, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_382 :
    scalarCheck (table.cell ⟨382, by decide⟩) = true := by
  kernel_decide

theorem certificate_382 :
    Certificate (table.cell ⟨382, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_382,
    crossing_of_check crossingCheck_382,
    scalar_of_check scalarCheck_382⟩

end Erdos1038.HighKPlatformConstantTableChunk382
