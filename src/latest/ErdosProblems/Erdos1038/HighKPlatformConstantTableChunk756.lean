import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 756 through 756. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk756

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_756 :
    geometryCheck (table.cell ⟨756, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_756 :
    crossingCheck (table.cell ⟨756, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_756 :
    scalarCheck (table.cell ⟨756, by decide⟩) = true := by
  kernel_decide

theorem certificate_756 :
    Certificate (table.cell ⟨756, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_756,
    crossing_of_check crossingCheck_756,
    scalar_of_check scalarCheck_756⟩

end Erdos1038.HighKPlatformConstantTableChunk756
