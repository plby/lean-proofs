import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 443 through 443. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk443

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_443 :
    geometryCheck (table.cell ⟨443, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_443 :
    crossingCheck (table.cell ⟨443, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_443 :
    scalarCheck (table.cell ⟨443, by decide⟩) = true := by
  kernel_decide

theorem certificate_443 :
    Certificate (table.cell ⟨443, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_443,
    crossing_of_check crossingCheck_443,
    scalar_of_check scalarCheck_443⟩

end Erdos1038.HighKPlatformConstantTableChunk443
