import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 684 through 684. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk684

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_684 :
    geometryCheck (table.cell ⟨684, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_684 :
    crossingCheck (table.cell ⟨684, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_684 :
    scalarCheck (table.cell ⟨684, by decide⟩) = true := by
  kernel_decide

theorem certificate_684 :
    Certificate (table.cell ⟨684, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_684,
    crossing_of_check crossingCheck_684,
    scalar_of_check scalarCheck_684⟩

end Erdos1038.HighKPlatformConstantTableChunk684
