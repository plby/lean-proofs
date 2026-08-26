import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 423 through 423. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk423

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_423 :
    geometryCheck (table.cell ⟨423, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_423 :
    crossingCheck (table.cell ⟨423, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_423 :
    scalarCheck (table.cell ⟨423, by decide⟩) = true := by
  kernel_decide

theorem certificate_423 :
    Certificate (table.cell ⟨423, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_423,
    crossing_of_check crossingCheck_423,
    scalar_of_check scalarCheck_423⟩

end Erdos1038.HighKPlatformConstantTableChunk423
