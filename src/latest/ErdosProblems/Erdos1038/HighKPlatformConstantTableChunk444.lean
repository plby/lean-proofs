import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 444 through 444. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk444

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_444 :
    geometryCheck (table.cell ⟨444, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_444 :
    crossingCheck (table.cell ⟨444, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_444 :
    scalarCheck (table.cell ⟨444, by decide⟩) = true := by
  kernel_decide

theorem certificate_444 :
    Certificate (table.cell ⟨444, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_444,
    crossing_of_check crossingCheck_444,
    scalar_of_check scalarCheck_444⟩

end Erdos1038.HighKPlatformConstantTableChunk444
