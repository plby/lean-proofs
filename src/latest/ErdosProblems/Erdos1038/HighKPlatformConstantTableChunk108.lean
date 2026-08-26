import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 108 through 108. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk108

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_108 :
    geometryCheck (table.cell ⟨108, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_108 :
    crossingCheck (table.cell ⟨108, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_108 :
    scalarCheck (table.cell ⟨108, by decide⟩) = true := by
  kernel_decide

theorem certificate_108 :
    Certificate (table.cell ⟨108, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_108,
    crossing_of_check crossingCheck_108,
    scalar_of_check scalarCheck_108⟩

end Erdos1038.HighKPlatformConstantTableChunk108
