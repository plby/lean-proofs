import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 637 through 637. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk637

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_637 :
    geometryCheck (table.cell ⟨637, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_637 :
    crossingCheck (table.cell ⟨637, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_637 :
    scalarCheck (table.cell ⟨637, by decide⟩) = true := by
  kernel_decide

theorem certificate_637 :
    Certificate (table.cell ⟨637, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_637,
    crossing_of_check crossingCheck_637,
    scalar_of_check scalarCheck_637⟩

end Erdos1038.HighKPlatformConstantTableChunk637
