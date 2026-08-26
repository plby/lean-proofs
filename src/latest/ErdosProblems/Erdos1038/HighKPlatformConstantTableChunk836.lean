import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 836 through 836. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk836

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_836 :
    geometryCheck (table.cell ⟨836, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_836 :
    crossingCheck (table.cell ⟨836, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_836 :
    scalarCheck (table.cell ⟨836, by decide⟩) = true := by
  kernel_decide

theorem certificate_836 :
    Certificate (table.cell ⟨836, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_836,
    crossing_of_check crossingCheck_836,
    scalar_of_check scalarCheck_836⟩

end Erdos1038.HighKPlatformConstantTableChunk836
