import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 772 through 772. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk772

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_772 :
    geometryCheck (table.cell ⟨772, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_772 :
    crossingCheck (table.cell ⟨772, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_772 :
    scalarCheck (table.cell ⟨772, by decide⟩) = true := by
  kernel_decide

theorem certificate_772 :
    Certificate (table.cell ⟨772, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_772,
    crossing_of_check crossingCheck_772,
    scalar_of_check scalarCheck_772⟩

end Erdos1038.HighKPlatformConstantTableChunk772
