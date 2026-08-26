import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 510 through 510. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk510

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_510 :
    geometryCheck (table.cell ⟨510, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_510 :
    crossingCheck (table.cell ⟨510, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_510 :
    scalarCheck (table.cell ⟨510, by decide⟩) = true := by
  kernel_decide

theorem certificate_510 :
    Certificate (table.cell ⟨510, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_510,
    crossing_of_check crossingCheck_510,
    scalar_of_check scalarCheck_510⟩

end Erdos1038.HighKPlatformConstantTableChunk510
