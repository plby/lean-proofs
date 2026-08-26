import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 88 through 88. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk88

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_088 :
    geometryCheck (table.cell ⟨88, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_088 :
    crossingCheck (table.cell ⟨88, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_088 :
    scalarCheck (table.cell ⟨88, by decide⟩) = true := by
  kernel_decide

theorem certificate_088 :
    Certificate (table.cell ⟨88, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_088,
    crossing_of_check crossingCheck_088,
    scalar_of_check scalarCheck_088⟩

end Erdos1038.HighKPlatformConstantTableChunk88
