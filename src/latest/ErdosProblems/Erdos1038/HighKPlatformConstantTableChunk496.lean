import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 496 through 496. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk496

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_496 :
    geometryCheck (table.cell ⟨496, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_496 :
    crossingCheck (table.cell ⟨496, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_496 :
    scalarCheck (table.cell ⟨496, by decide⟩) = true := by
  kernel_decide

theorem certificate_496 :
    Certificate (table.cell ⟨496, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_496,
    crossing_of_check crossingCheck_496,
    scalar_of_check scalarCheck_496⟩

end Erdos1038.HighKPlatformConstantTableChunk496
