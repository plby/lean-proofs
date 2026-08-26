import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 655 through 655. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk655

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_655 :
    geometryCheck (table.cell ⟨655, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_655 :
    crossingCheck (table.cell ⟨655, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_655 :
    scalarCheck (table.cell ⟨655, by decide⟩) = true := by
  kernel_decide

theorem certificate_655 :
    Certificate (table.cell ⟨655, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_655,
    crossing_of_check crossingCheck_655,
    scalar_of_check scalarCheck_655⟩

end Erdos1038.HighKPlatformConstantTableChunk655
