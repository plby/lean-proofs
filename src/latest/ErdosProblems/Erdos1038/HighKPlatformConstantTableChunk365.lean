import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 365 through 365. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk365

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_365 :
    geometryCheck (table.cell ⟨365, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_365 :
    crossingCheck (table.cell ⟨365, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_365 :
    scalarCheck (table.cell ⟨365, by decide⟩) = true := by
  kernel_decide

theorem certificate_365 :
    Certificate (table.cell ⟨365, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_365,
    crossing_of_check crossingCheck_365,
    scalar_of_check scalarCheck_365⟩

end Erdos1038.HighKPlatformConstantTableChunk365
