import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 573 through 573. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk573

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_573 :
    geometryCheck (table.cell ⟨573, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_573 :
    crossingCheck (table.cell ⟨573, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_573 :
    scalarCheck (table.cell ⟨573, by decide⟩) = true := by
  kernel_decide

theorem certificate_573 :
    Certificate (table.cell ⟨573, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_573,
    crossing_of_check crossingCheck_573,
    scalar_of_check scalarCheck_573⟩

end Erdos1038.HighKPlatformConstantTableChunk573
