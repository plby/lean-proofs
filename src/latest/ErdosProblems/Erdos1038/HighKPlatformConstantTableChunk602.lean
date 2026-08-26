import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 602 through 602. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk602

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_602 :
    geometryCheck (table.cell ⟨602, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_602 :
    crossingCheck (table.cell ⟨602, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_602 :
    scalarCheck (table.cell ⟨602, by decide⟩) = true := by
  kernel_decide

theorem certificate_602 :
    Certificate (table.cell ⟨602, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_602,
    crossing_of_check crossingCheck_602,
    scalar_of_check scalarCheck_602⟩

end Erdos1038.HighKPlatformConstantTableChunk602
