import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 614 through 614. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk614

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_614 :
    geometryCheck (table.cell ⟨614, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_614 :
    crossingCheck (table.cell ⟨614, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_614 :
    scalarCheck (table.cell ⟨614, by decide⟩) = true := by
  kernel_decide

theorem certificate_614 :
    Certificate (table.cell ⟨614, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_614,
    crossing_of_check crossingCheck_614,
    scalar_of_check scalarCheck_614⟩

end Erdos1038.HighKPlatformConstantTableChunk614
