import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 13 through 13. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk13

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_013 :
    geometryCheck (table.cell ⟨13, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_013 :
    crossingCheck (table.cell ⟨13, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_013 :
    scalarCheck (table.cell ⟨13, by decide⟩) = true := by
  kernel_decide

theorem certificate_013 :
    Certificate (table.cell ⟨13, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_013,
    crossing_of_check crossingCheck_013,
    scalar_of_check scalarCheck_013⟩

end Erdos1038.HighKPlatformConstantTableChunk13
