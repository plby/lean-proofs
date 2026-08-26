import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 308 through 308. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk308

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_308 :
    geometryCheck (table.cell ⟨308, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_308 :
    crossingCheck (table.cell ⟨308, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_308 :
    scalarCheck (table.cell ⟨308, by decide⟩) = true := by
  kernel_decide

theorem certificate_308 :
    Certificate (table.cell ⟨308, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_308,
    crossing_of_check crossingCheck_308,
    scalar_of_check scalarCheck_308⟩

end Erdos1038.HighKPlatformConstantTableChunk308
