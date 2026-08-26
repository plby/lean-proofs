import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 121 through 121. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk121

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_121 :
    geometryCheck (table.cell ⟨121, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_121 :
    crossingCheck (table.cell ⟨121, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_121 :
    scalarCheck (table.cell ⟨121, by decide⟩) = true := by
  kernel_decide

theorem certificate_121 :
    Certificate (table.cell ⟨121, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_121,
    crossing_of_check crossingCheck_121,
    scalar_of_check scalarCheck_121⟩

end Erdos1038.HighKPlatformConstantTableChunk121
