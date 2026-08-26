import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 484 through 484. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk484

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_484 :
    geometryCheck (table.cell ⟨484, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_484 :
    crossingCheck (table.cell ⟨484, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_484 :
    scalarCheck (table.cell ⟨484, by decide⟩) = true := by
  kernel_decide

theorem certificate_484 :
    Certificate (table.cell ⟨484, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_484,
    crossing_of_check crossingCheck_484,
    scalar_of_check scalarCheck_484⟩

end Erdos1038.HighKPlatformConstantTableChunk484
