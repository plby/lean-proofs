import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 619 through 619. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk619

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_619 :
    geometryCheck (table.cell ⟨619, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_619 :
    crossingCheck (table.cell ⟨619, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_619 :
    scalarCheck (table.cell ⟨619, by decide⟩) = true := by
  kernel_decide

theorem certificate_619 :
    Certificate (table.cell ⟨619, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_619,
    crossing_of_check crossingCheck_619,
    scalar_of_check scalarCheck_619⟩

end Erdos1038.HighKPlatformConstantTableChunk619
