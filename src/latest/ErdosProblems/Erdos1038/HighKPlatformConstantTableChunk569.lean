import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 569 through 569. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk569

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_569 :
    geometryCheck (table.cell ⟨569, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_569 :
    crossingCheck (table.cell ⟨569, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_569 :
    scalarCheck (table.cell ⟨569, by decide⟩) = true := by
  kernel_decide

theorem certificate_569 :
    Certificate (table.cell ⟨569, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_569,
    crossing_of_check crossingCheck_569,
    scalar_of_check scalarCheck_569⟩

end Erdos1038.HighKPlatformConstantTableChunk569
