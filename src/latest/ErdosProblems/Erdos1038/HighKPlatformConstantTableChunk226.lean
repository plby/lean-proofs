import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 226 through 226. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk226

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_226 :
    geometryCheck (table.cell ⟨226, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_226 :
    crossingCheck (table.cell ⟨226, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_226 :
    scalarCheck (table.cell ⟨226, by decide⟩) = true := by
  kernel_decide

theorem certificate_226 :
    Certificate (table.cell ⟨226, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_226,
    crossing_of_check crossingCheck_226,
    scalar_of_check scalarCheck_226⟩

end Erdos1038.HighKPlatformConstantTableChunk226
