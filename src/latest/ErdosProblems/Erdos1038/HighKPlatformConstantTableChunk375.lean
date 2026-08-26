import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 375 through 375. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk375

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_375 :
    geometryCheck (table.cell ⟨375, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_375 :
    crossingCheck (table.cell ⟨375, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_375 :
    scalarCheck (table.cell ⟨375, by decide⟩) = true := by
  kernel_decide

theorem certificate_375 :
    Certificate (table.cell ⟨375, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_375,
    crossing_of_check crossingCheck_375,
    scalar_of_check scalarCheck_375⟩

end Erdos1038.HighKPlatformConstantTableChunk375
