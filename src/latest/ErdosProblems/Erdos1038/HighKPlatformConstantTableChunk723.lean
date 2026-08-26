import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 723 through 723. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk723

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_723 :
    geometryCheck (table.cell ⟨723, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_723 :
    crossingCheck (table.cell ⟨723, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_723 :
    scalarCheck (table.cell ⟨723, by decide⟩) = true := by
  kernel_decide

theorem certificate_723 :
    Certificate (table.cell ⟨723, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_723,
    crossing_of_check crossingCheck_723,
    scalar_of_check scalarCheck_723⟩

end Erdos1038.HighKPlatformConstantTableChunk723
