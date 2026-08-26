import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 627 through 627. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk627

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_627 :
    geometryCheck (table.cell ⟨627, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_627 :
    crossingCheck (table.cell ⟨627, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_627 :
    scalarCheck (table.cell ⟨627, by decide⟩) = true := by
  kernel_decide

theorem certificate_627 :
    Certificate (table.cell ⟨627, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_627,
    crossing_of_check crossingCheck_627,
    scalar_of_check scalarCheck_627⟩

end Erdos1038.HighKPlatformConstantTableChunk627
