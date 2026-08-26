import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 728 through 728. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk728

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_728 :
    geometryCheck (table.cell ⟨728, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_728 :
    crossingCheck (table.cell ⟨728, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_728 :
    scalarCheck (table.cell ⟨728, by decide⟩) = true := by
  kernel_decide

theorem certificate_728 :
    Certificate (table.cell ⟨728, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_728,
    crossing_of_check crossingCheck_728,
    scalar_of_check scalarCheck_728⟩

end Erdos1038.HighKPlatformConstantTableChunk728
