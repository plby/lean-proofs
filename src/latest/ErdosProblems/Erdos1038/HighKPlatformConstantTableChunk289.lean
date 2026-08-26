import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 289 through 289. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk289

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_289 :
    geometryCheck (table.cell ⟨289, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_289 :
    crossingCheck (table.cell ⟨289, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_289 :
    scalarCheck (table.cell ⟨289, by decide⟩) = true := by
  kernel_decide

theorem certificate_289 :
    Certificate (table.cell ⟨289, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_289,
    crossing_of_check crossingCheck_289,
    scalar_of_check scalarCheck_289⟩

end Erdos1038.HighKPlatformConstantTableChunk289
