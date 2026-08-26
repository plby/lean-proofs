import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 54 through 54. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk54

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_054 :
    geometryCheck (table.cell ⟨54, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_054 :
    crossingCheck (table.cell ⟨54, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_054 :
    scalarCheck (table.cell ⟨54, by decide⟩) = true := by
  kernel_decide

theorem certificate_054 :
    Certificate (table.cell ⟨54, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_054,
    crossing_of_check crossingCheck_054,
    scalar_of_check scalarCheck_054⟩

end Erdos1038.HighKPlatformConstantTableChunk54
