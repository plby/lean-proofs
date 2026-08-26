import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 55 through 55. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk55

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_055 :
    geometryCheck (table.cell ⟨55, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_055 :
    crossingCheck (table.cell ⟨55, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_055 :
    scalarCheck (table.cell ⟨55, by decide⟩) = true := by
  kernel_decide

theorem certificate_055 :
    Certificate (table.cell ⟨55, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_055,
    crossing_of_check crossingCheck_055,
    scalar_of_check scalarCheck_055⟩

end Erdos1038.HighKPlatformConstantTableChunk55
