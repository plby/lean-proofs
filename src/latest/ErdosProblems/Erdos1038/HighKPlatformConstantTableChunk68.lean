import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 68 through 68. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk68

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_068 :
    geometryCheck (table.cell ⟨68, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_068 :
    crossingCheck (table.cell ⟨68, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_068 :
    scalarCheck (table.cell ⟨68, by decide⟩) = true := by
  kernel_decide

theorem certificate_068 :
    Certificate (table.cell ⟨68, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_068,
    crossing_of_check crossingCheck_068,
    scalar_of_check scalarCheck_068⟩

end Erdos1038.HighKPlatformConstantTableChunk68
