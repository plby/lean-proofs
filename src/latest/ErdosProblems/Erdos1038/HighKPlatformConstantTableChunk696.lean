import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 696 through 696. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk696

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_696 :
    geometryCheck (table.cell ⟨696, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_696 :
    crossingCheck (table.cell ⟨696, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_696 :
    scalarCheck (table.cell ⟨696, by decide⟩) = true := by
  kernel_decide

theorem certificate_696 :
    Certificate (table.cell ⟨696, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_696,
    crossing_of_check crossingCheck_696,
    scalar_of_check scalarCheck_696⟩

end Erdos1038.HighKPlatformConstantTableChunk696
