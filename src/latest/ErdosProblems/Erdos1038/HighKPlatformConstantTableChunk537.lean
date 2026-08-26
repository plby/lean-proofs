import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 537 through 537. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk537

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_537 :
    geometryCheck (table.cell ⟨537, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_537 :
    crossingCheck (table.cell ⟨537, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_537 :
    scalarCheck (table.cell ⟨537, by decide⟩) = true := by
  kernel_decide

theorem certificate_537 :
    Certificate (table.cell ⟨537, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_537,
    crossing_of_check crossingCheck_537,
    scalar_of_check scalarCheck_537⟩

end Erdos1038.HighKPlatformConstantTableChunk537
