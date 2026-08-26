import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 610 through 610. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk610

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_610 :
    geometryCheck (table.cell ⟨610, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_610 :
    crossingCheck (table.cell ⟨610, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_610 :
    scalarCheck (table.cell ⟨610, by decide⟩) = true := by
  kernel_decide

theorem certificate_610 :
    Certificate (table.cell ⟨610, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_610,
    crossing_of_check crossingCheck_610,
    scalar_of_check scalarCheck_610⟩

end Erdos1038.HighKPlatformConstantTableChunk610
