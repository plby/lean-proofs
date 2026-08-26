import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 583 through 583. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk583

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_583 :
    geometryCheck (table.cell ⟨583, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_583 :
    crossingCheck (table.cell ⟨583, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_583 :
    scalarCheck (table.cell ⟨583, by decide⟩) = true := by
  kernel_decide

theorem certificate_583 :
    Certificate (table.cell ⟨583, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_583,
    crossing_of_check crossingCheck_583,
    scalar_of_check scalarCheck_583⟩

end Erdos1038.HighKPlatformConstantTableChunk583
