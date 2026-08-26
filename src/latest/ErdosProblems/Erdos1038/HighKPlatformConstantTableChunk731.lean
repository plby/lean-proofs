import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 731 through 731. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk731

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_731 :
    geometryCheck (table.cell ⟨731, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_731 :
    crossingCheck (table.cell ⟨731, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_731 :
    scalarCheck (table.cell ⟨731, by decide⟩) = true := by
  kernel_decide

theorem certificate_731 :
    Certificate (table.cell ⟨731, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_731,
    crossing_of_check crossingCheck_731,
    scalar_of_check scalarCheck_731⟩

end Erdos1038.HighKPlatformConstantTableChunk731
