import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 738 through 738. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk738

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_738 :
    geometryCheck (table.cell ⟨738, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_738 :
    crossingCheck (table.cell ⟨738, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_738 :
    scalarCheck (table.cell ⟨738, by decide⟩) = true := by
  kernel_decide

theorem certificate_738 :
    Certificate (table.cell ⟨738, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_738,
    crossing_of_check crossingCheck_738,
    scalar_of_check scalarCheck_738⟩

end Erdos1038.HighKPlatformConstantTableChunk738
