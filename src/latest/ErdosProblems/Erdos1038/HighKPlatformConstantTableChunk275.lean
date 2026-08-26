import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 275 through 275. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk275

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_275 :
    geometryCheck (table.cell ⟨275, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_275 :
    crossingCheck (table.cell ⟨275, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_275 :
    scalarCheck (table.cell ⟨275, by decide⟩) = true := by
  kernel_decide

theorem certificate_275 :
    Certificate (table.cell ⟨275, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_275,
    crossing_of_check crossingCheck_275,
    scalar_of_check scalarCheck_275⟩

end Erdos1038.HighKPlatformConstantTableChunk275
