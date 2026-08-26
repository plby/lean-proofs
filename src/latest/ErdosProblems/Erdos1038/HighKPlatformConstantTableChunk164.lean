import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 164 through 164. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk164

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_164 :
    geometryCheck (table.cell ⟨164, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_164 :
    crossingCheck (table.cell ⟨164, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_164 :
    scalarCheck (table.cell ⟨164, by decide⟩) = true := by
  kernel_decide

theorem certificate_164 :
    Certificate (table.cell ⟨164, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_164,
    crossing_of_check crossingCheck_164,
    scalar_of_check scalarCheck_164⟩

end Erdos1038.HighKPlatformConstantTableChunk164
