import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 834 through 834. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk834

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_834 :
    geometryCheck (table.cell ⟨834, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_834 :
    crossingCheck (table.cell ⟨834, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_834 :
    scalarCheck (table.cell ⟨834, by decide⟩) = true := by
  kernel_decide

theorem certificate_834 :
    Certificate (table.cell ⟨834, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_834,
    crossing_of_check crossingCheck_834,
    scalar_of_check scalarCheck_834⟩

end Erdos1038.HighKPlatformConstantTableChunk834
