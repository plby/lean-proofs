import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 528 through 528. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk528

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_528 :
    geometryCheck (table.cell ⟨528, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_528 :
    crossingCheck (table.cell ⟨528, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_528 :
    scalarCheck (table.cell ⟨528, by decide⟩) = true := by
  kernel_decide

theorem certificate_528 :
    Certificate (table.cell ⟨528, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_528,
    crossing_of_check crossingCheck_528,
    scalar_of_check scalarCheck_528⟩

end Erdos1038.HighKPlatformConstantTableChunk528
