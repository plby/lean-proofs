import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 651 through 651. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk651

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_651 :
    geometryCheck (table.cell ⟨651, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_651 :
    crossingCheck (table.cell ⟨651, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_651 :
    scalarCheck (table.cell ⟨651, by decide⟩) = true := by
  kernel_decide

theorem certificate_651 :
    Certificate (table.cell ⟨651, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_651,
    crossing_of_check crossingCheck_651,
    scalar_of_check scalarCheck_651⟩

end Erdos1038.HighKPlatformConstantTableChunk651
