import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 683 through 683. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk683

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_683 :
    geometryCheck (table.cell ⟨683, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_683 :
    crossingCheck (table.cell ⟨683, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_683 :
    scalarCheck (table.cell ⟨683, by decide⟩) = true := by
  kernel_decide

theorem certificate_683 :
    Certificate (table.cell ⟨683, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_683,
    crossing_of_check crossingCheck_683,
    scalar_of_check scalarCheck_683⟩

end Erdos1038.HighKPlatformConstantTableChunk683
