import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 579 through 579. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk579

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_579 :
    geometryCheck (table.cell ⟨579, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_579 :
    crossingCheck (table.cell ⟨579, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_579 :
    scalarCheck (table.cell ⟨579, by decide⟩) = true := by
  kernel_decide

theorem certificate_579 :
    Certificate (table.cell ⟨579, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_579,
    crossing_of_check crossingCheck_579,
    scalar_of_check scalarCheck_579⟩

end Erdos1038.HighKPlatformConstantTableChunk579
