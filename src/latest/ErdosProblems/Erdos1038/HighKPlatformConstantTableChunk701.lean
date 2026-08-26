import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 701 through 701. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk701

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_701 :
    geometryCheck (table.cell ⟨701, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_701 :
    crossingCheck (table.cell ⟨701, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_701 :
    scalarCheck (table.cell ⟨701, by decide⟩) = true := by
  kernel_decide

theorem certificate_701 :
    Certificate (table.cell ⟨701, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_701,
    crossing_of_check crossingCheck_701,
    scalar_of_check scalarCheck_701⟩

end Erdos1038.HighKPlatformConstantTableChunk701
