import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 449 through 449. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk449

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_449 :
    geometryCheck (table.cell ⟨449, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_449 :
    crossingCheck (table.cell ⟨449, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_449 :
    scalarCheck (table.cell ⟨449, by decide⟩) = true := by
  kernel_decide

theorem certificate_449 :
    Certificate (table.cell ⟨449, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_449,
    crossing_of_check crossingCheck_449,
    scalar_of_check scalarCheck_449⟩

end Erdos1038.HighKPlatformConstantTableChunk449
