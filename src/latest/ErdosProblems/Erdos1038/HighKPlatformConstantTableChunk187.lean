import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 187 through 187. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk187

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_187 :
    geometryCheck (table.cell ⟨187, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_187 :
    crossingCheck (table.cell ⟨187, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_187 :
    scalarCheck (table.cell ⟨187, by decide⟩) = true := by
  kernel_decide

theorem certificate_187 :
    Certificate (table.cell ⟨187, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_187,
    crossing_of_check crossingCheck_187,
    scalar_of_check scalarCheck_187⟩

end Erdos1038.HighKPlatformConstantTableChunk187
