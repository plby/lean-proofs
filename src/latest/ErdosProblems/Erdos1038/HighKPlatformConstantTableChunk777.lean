import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 777 through 777. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk777

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_777 :
    geometryCheck (table.cell ⟨777, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_777 :
    crossingCheck (table.cell ⟨777, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_777 :
    scalarCheck (table.cell ⟨777, by decide⟩) = true := by
  kernel_decide

theorem certificate_777 :
    Certificate (table.cell ⟨777, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_777,
    crossing_of_check crossingCheck_777,
    scalar_of_check scalarCheck_777⟩

end Erdos1038.HighKPlatformConstantTableChunk777
