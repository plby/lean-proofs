import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 546 through 546. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk546

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_546 :
    geometryCheck (table.cell ⟨546, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_546 :
    crossingCheck (table.cell ⟨546, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_546 :
    scalarCheck (table.cell ⟨546, by decide⟩) = true := by
  kernel_decide

theorem certificate_546 :
    Certificate (table.cell ⟨546, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_546,
    crossing_of_check crossingCheck_546,
    scalar_of_check scalarCheck_546⟩

end Erdos1038.HighKPlatformConstantTableChunk546
