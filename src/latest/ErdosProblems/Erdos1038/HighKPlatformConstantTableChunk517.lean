import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 517 through 517. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk517

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_517 :
    geometryCheck (table.cell ⟨517, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_517 :
    crossingCheck (table.cell ⟨517, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_517 :
    scalarCheck (table.cell ⟨517, by decide⟩) = true := by
  kernel_decide

theorem certificate_517 :
    Certificate (table.cell ⟨517, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_517,
    crossing_of_check crossingCheck_517,
    scalar_of_check scalarCheck_517⟩

end Erdos1038.HighKPlatformConstantTableChunk517
