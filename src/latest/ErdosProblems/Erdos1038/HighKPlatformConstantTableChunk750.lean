import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 750 through 750. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk750

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_750 :
    geometryCheck (table.cell ⟨750, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_750 :
    crossingCheck (table.cell ⟨750, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_750 :
    scalarCheck (table.cell ⟨750, by decide⟩) = true := by
  kernel_decide

theorem certificate_750 :
    Certificate (table.cell ⟨750, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_750,
    crossing_of_check crossingCheck_750,
    scalar_of_check scalarCheck_750⟩

end Erdos1038.HighKPlatformConstantTableChunk750
