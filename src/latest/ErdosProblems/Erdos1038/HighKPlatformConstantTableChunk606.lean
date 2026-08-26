import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 606 through 606. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk606

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_606 :
    geometryCheck (table.cell ⟨606, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_606 :
    crossingCheck (table.cell ⟨606, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_606 :
    scalarCheck (table.cell ⟨606, by decide⟩) = true := by
  kernel_decide

theorem certificate_606 :
    Certificate (table.cell ⟨606, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_606,
    crossing_of_check crossingCheck_606,
    scalar_of_check scalarCheck_606⟩

end Erdos1038.HighKPlatformConstantTableChunk606
