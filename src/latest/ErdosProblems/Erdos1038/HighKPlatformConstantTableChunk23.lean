import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 23 through 23. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk23

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_023 :
    geometryCheck (table.cell ⟨23, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_023 :
    crossingCheck (table.cell ⟨23, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_023 :
    scalarCheck (table.cell ⟨23, by decide⟩) = true := by
  kernel_decide

theorem certificate_023 :
    Certificate (table.cell ⟨23, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_023,
    crossing_of_check crossingCheck_023,
    scalar_of_check scalarCheck_023⟩

end Erdos1038.HighKPlatformConstantTableChunk23
