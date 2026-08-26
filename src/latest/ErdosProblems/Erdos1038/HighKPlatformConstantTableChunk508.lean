import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 508 through 508. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk508

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_508 :
    geometryCheck (table.cell ⟨508, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_508 :
    crossingCheck (table.cell ⟨508, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_508 :
    scalarCheck (table.cell ⟨508, by decide⟩) = true := by
  kernel_decide

theorem certificate_508 :
    Certificate (table.cell ⟨508, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_508,
    crossing_of_check crossingCheck_508,
    scalar_of_check scalarCheck_508⟩

end Erdos1038.HighKPlatformConstantTableChunk508
