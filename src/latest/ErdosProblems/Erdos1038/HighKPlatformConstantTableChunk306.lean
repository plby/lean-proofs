import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 306 through 306. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk306

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_306 :
    geometryCheck (table.cell ⟨306, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_306 :
    crossingCheck (table.cell ⟨306, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_306 :
    scalarCheck (table.cell ⟨306, by decide⟩) = true := by
  kernel_decide

theorem certificate_306 :
    Certificate (table.cell ⟨306, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_306,
    crossing_of_check crossingCheck_306,
    scalar_of_check scalarCheck_306⟩

end Erdos1038.HighKPlatformConstantTableChunk306
