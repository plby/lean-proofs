import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 225 through 225. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk225

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_225 :
    geometryCheck (table.cell ⟨225, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_225 :
    crossingCheck (table.cell ⟨225, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_225 :
    scalarCheck (table.cell ⟨225, by decide⟩) = true := by
  kernel_decide

theorem certificate_225 :
    Certificate (table.cell ⟨225, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_225,
    crossing_of_check crossingCheck_225,
    scalar_of_check scalarCheck_225⟩

end Erdos1038.HighKPlatformConstantTableChunk225
