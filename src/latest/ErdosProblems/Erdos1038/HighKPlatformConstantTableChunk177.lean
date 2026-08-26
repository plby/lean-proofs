import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 177 through 177. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk177

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_177 :
    geometryCheck (table.cell ⟨177, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_177 :
    crossingCheck (table.cell ⟨177, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_177 :
    scalarCheck (table.cell ⟨177, by decide⟩) = true := by
  kernel_decide

theorem certificate_177 :
    Certificate (table.cell ⟨177, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_177,
    crossing_of_check crossingCheck_177,
    scalar_of_check scalarCheck_177⟩

end Erdos1038.HighKPlatformConstantTableChunk177
