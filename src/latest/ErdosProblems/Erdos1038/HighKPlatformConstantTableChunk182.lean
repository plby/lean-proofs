import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 182 through 182. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk182

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_182 :
    geometryCheck (table.cell ⟨182, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_182 :
    crossingCheck (table.cell ⟨182, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_182 :
    scalarCheck (table.cell ⟨182, by decide⟩) = true := by
  kernel_decide

theorem certificate_182 :
    Certificate (table.cell ⟨182, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_182,
    crossing_of_check crossingCheck_182,
    scalar_of_check scalarCheck_182⟩

end Erdos1038.HighKPlatformConstantTableChunk182
