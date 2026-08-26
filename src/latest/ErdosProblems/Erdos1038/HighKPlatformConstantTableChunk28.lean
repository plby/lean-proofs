import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 28 through 28. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk28

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_028 :
    geometryCheck (table.cell ⟨28, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_028 :
    crossingCheck (table.cell ⟨28, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_028 :
    scalarCheck (table.cell ⟨28, by decide⟩) = true := by
  kernel_decide

theorem certificate_028 :
    Certificate (table.cell ⟨28, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_028,
    crossing_of_check crossingCheck_028,
    scalar_of_check scalarCheck_028⟩

end Erdos1038.HighKPlatformConstantTableChunk28
