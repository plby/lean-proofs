import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 591 through 591. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk591

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_591 :
    geometryCheck (table.cell ⟨591, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_591 :
    crossingCheck (table.cell ⟨591, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_591 :
    scalarCheck (table.cell ⟨591, by decide⟩) = true := by
  kernel_decide

theorem certificate_591 :
    Certificate (table.cell ⟨591, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_591,
    crossing_of_check crossingCheck_591,
    scalar_of_check scalarCheck_591⟩

end Erdos1038.HighKPlatformConstantTableChunk591
