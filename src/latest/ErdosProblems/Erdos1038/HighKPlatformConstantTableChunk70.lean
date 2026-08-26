import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 70 through 70. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk70

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_070 :
    geometryCheck (table.cell ⟨70, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_070 :
    crossingCheck (table.cell ⟨70, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_070 :
    scalarCheck (table.cell ⟨70, by decide⟩) = true := by
  kernel_decide

theorem certificate_070 :
    Certificate (table.cell ⟨70, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_070,
    crossing_of_check crossingCheck_070,
    scalar_of_check scalarCheck_070⟩

end Erdos1038.HighKPlatformConstantTableChunk70
