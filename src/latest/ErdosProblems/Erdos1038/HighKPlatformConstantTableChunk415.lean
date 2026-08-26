import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 415 through 415. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk415

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_415 :
    geometryCheck (table.cell ⟨415, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_415 :
    crossingCheck (table.cell ⟨415, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_415 :
    scalarCheck (table.cell ⟨415, by decide⟩) = true := by
  kernel_decide

theorem certificate_415 :
    Certificate (table.cell ⟨415, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_415,
    crossing_of_check crossingCheck_415,
    scalar_of_check scalarCheck_415⟩

end Erdos1038.HighKPlatformConstantTableChunk415
