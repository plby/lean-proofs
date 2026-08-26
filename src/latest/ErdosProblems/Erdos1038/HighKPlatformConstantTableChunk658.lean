import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 658 through 658. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk658

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_658 :
    geometryCheck (table.cell ⟨658, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_658 :
    crossingCheck (table.cell ⟨658, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_658 :
    scalarCheck (table.cell ⟨658, by decide⟩) = true := by
  kernel_decide

theorem certificate_658 :
    Certificate (table.cell ⟨658, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_658,
    crossing_of_check crossingCheck_658,
    scalar_of_check scalarCheck_658⟩

end Erdos1038.HighKPlatformConstantTableChunk658
