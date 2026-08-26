import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 553 through 553. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk553

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_553 :
    geometryCheck (table.cell ⟨553, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_553 :
    crossingCheck (table.cell ⟨553, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_553 :
    scalarCheck (table.cell ⟨553, by decide⟩) = true := by
  kernel_decide

theorem certificate_553 :
    Certificate (table.cell ⟨553, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_553,
    crossing_of_check crossingCheck_553,
    scalar_of_check scalarCheck_553⟩

end Erdos1038.HighKPlatformConstantTableChunk553
