import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 34 through 34. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk34

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_034 :
    geometryCheck (table.cell ⟨34, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_034 :
    crossingCheck (table.cell ⟨34, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_034 :
    scalarCheck (table.cell ⟨34, by decide⟩) = true := by
  kernel_decide

theorem certificate_034 :
    Certificate (table.cell ⟨34, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_034,
    crossing_of_check crossingCheck_034,
    scalar_of_check scalarCheck_034⟩

end Erdos1038.HighKPlatformConstantTableChunk34
