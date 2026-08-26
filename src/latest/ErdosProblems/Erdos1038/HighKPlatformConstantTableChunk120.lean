import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 120 through 120. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk120

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_120 :
    geometryCheck (table.cell ⟨120, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_120 :
    crossingCheck (table.cell ⟨120, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_120 :
    scalarCheck (table.cell ⟨120, by decide⟩) = true := by
  kernel_decide

theorem certificate_120 :
    Certificate (table.cell ⟨120, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_120,
    crossing_of_check crossingCheck_120,
    scalar_of_check scalarCheck_120⟩

end Erdos1038.HighKPlatformConstantTableChunk120
