import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 568 through 568. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk568

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_568 :
    geometryCheck (table.cell ⟨568, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_568 :
    crossingCheck (table.cell ⟨568, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_568 :
    scalarCheck (table.cell ⟨568, by decide⟩) = true := by
  kernel_decide

theorem certificate_568 :
    Certificate (table.cell ⟨568, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_568,
    crossing_of_check crossingCheck_568,
    scalar_of_check scalarCheck_568⟩

end Erdos1038.HighKPlatformConstantTableChunk568
