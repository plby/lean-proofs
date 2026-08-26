import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 803 through 803. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk803

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_803 :
    geometryCheck (table.cell ⟨803, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_803 :
    crossingCheck (table.cell ⟨803, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_803 :
    scalarCheck (table.cell ⟨803, by decide⟩) = true := by
  kernel_decide

theorem certificate_803 :
    Certificate (table.cell ⟨803, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_803,
    crossing_of_check crossingCheck_803,
    scalar_of_check scalarCheck_803⟩

end Erdos1038.HighKPlatformConstantTableChunk803
