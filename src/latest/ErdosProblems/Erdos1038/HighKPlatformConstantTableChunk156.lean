import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 156 through 156. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk156

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_156 :
    geometryCheck (table.cell ⟨156, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_156 :
    crossingCheck (table.cell ⟨156, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_156 :
    scalarCheck (table.cell ⟨156, by decide⟩) = true := by
  kernel_decide

theorem certificate_156 :
    Certificate (table.cell ⟨156, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_156,
    crossing_of_check crossingCheck_156,
    scalar_of_check scalarCheck_156⟩

end Erdos1038.HighKPlatformConstantTableChunk156
