import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 325 through 325. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk325

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_325 :
    geometryCheck (table.cell ⟨325, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_325 :
    crossingCheck (table.cell ⟨325, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_325 :
    scalarCheck (table.cell ⟨325, by decide⟩) = true := by
  kernel_decide

theorem certificate_325 :
    Certificate (table.cell ⟨325, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_325,
    crossing_of_check crossingCheck_325,
    scalar_of_check scalarCheck_325⟩

end Erdos1038.HighKPlatformConstantTableChunk325
