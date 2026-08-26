import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 474 through 474. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk474

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_474 :
    geometryCheck (table.cell ⟨474, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_474 :
    crossingCheck (table.cell ⟨474, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_474 :
    scalarCheck (table.cell ⟨474, by decide⟩) = true := by
  kernel_decide

theorem certificate_474 :
    Certificate (table.cell ⟨474, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_474,
    crossing_of_check crossingCheck_474,
    scalar_of_check scalarCheck_474⟩

end Erdos1038.HighKPlatformConstantTableChunk474
