import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 747 through 747. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk747

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_747 :
    geometryCheck (table.cell ⟨747, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_747 :
    crossingCheck (table.cell ⟨747, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_747 :
    scalarCheck (table.cell ⟨747, by decide⟩) = true := by
  kernel_decide

theorem certificate_747 :
    Certificate (table.cell ⟨747, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_747,
    crossing_of_check crossingCheck_747,
    scalar_of_check scalarCheck_747⟩

end Erdos1038.HighKPlatformConstantTableChunk747
