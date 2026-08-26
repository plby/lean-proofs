import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 6 through 6. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk06

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_006 :
    geometryCheck (table.cell ⟨6, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_006 :
    crossingCheck (table.cell ⟨6, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_006 :
    scalarCheck (table.cell ⟨6, by decide⟩) = true := by
  kernel_decide

theorem certificate_006 :
    Certificate (table.cell ⟨6, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_006,
    crossing_of_check crossingCheck_006,
    scalar_of_check scalarCheck_006⟩

end Erdos1038.HighKPlatformConstantTableChunk06
