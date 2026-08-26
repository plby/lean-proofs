import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 521 through 521. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk521

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_521 :
    geometryCheck (table.cell ⟨521, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_521 :
    crossingCheck (table.cell ⟨521, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_521 :
    scalarCheck (table.cell ⟨521, by decide⟩) = true := by
  kernel_decide

theorem certificate_521 :
    Certificate (table.cell ⟨521, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_521,
    crossing_of_check crossingCheck_521,
    scalar_of_check scalarCheck_521⟩

end Erdos1038.HighKPlatformConstantTableChunk521
