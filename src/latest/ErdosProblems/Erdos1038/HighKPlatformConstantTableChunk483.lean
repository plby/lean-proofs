import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 483 through 483. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk483

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_483 :
    geometryCheck (table.cell ⟨483, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_483 :
    crossingCheck (table.cell ⟨483, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_483 :
    scalarCheck (table.cell ⟨483, by decide⟩) = true := by
  kernel_decide

theorem certificate_483 :
    Certificate (table.cell ⟨483, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_483,
    crossing_of_check crossingCheck_483,
    scalar_of_check scalarCheck_483⟩

end Erdos1038.HighKPlatformConstantTableChunk483
