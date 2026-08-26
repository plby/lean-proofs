import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 705 through 705. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk705

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_705 :
    geometryCheck (table.cell ⟨705, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_705 :
    crossingCheck (table.cell ⟨705, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_705 :
    scalarCheck (table.cell ⟨705, by decide⟩) = true := by
  kernel_decide

theorem certificate_705 :
    Certificate (table.cell ⟨705, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_705,
    crossing_of_check crossingCheck_705,
    scalar_of_check scalarCheck_705⟩

end Erdos1038.HighKPlatformConstantTableChunk705
