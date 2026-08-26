import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 549 through 549. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk549

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_549 :
    geometryCheck (table.cell ⟨549, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_549 :
    crossingCheck (table.cell ⟨549, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_549 :
    scalarCheck (table.cell ⟨549, by decide⟩) = true := by
  kernel_decide

theorem certificate_549 :
    Certificate (table.cell ⟨549, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_549,
    crossing_of_check crossingCheck_549,
    scalar_of_check scalarCheck_549⟩

end Erdos1038.HighKPlatformConstantTableChunk549
