import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 495 through 495. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk495

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_495 :
    geometryCheck (table.cell ⟨495, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_495 :
    crossingCheck (table.cell ⟨495, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_495 :
    scalarCheck (table.cell ⟨495, by decide⟩) = true := by
  kernel_decide

theorem certificate_495 :
    Certificate (table.cell ⟨495, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_495,
    crossing_of_check crossingCheck_495,
    scalar_of_check scalarCheck_495⟩

end Erdos1038.HighKPlatformConstantTableChunk495
