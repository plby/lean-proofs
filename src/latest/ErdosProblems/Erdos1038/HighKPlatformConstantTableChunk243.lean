import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 243 through 243. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk243

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_243 :
    geometryCheck (table.cell ⟨243, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_243 :
    crossingCheck (table.cell ⟨243, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_243 :
    scalarCheck (table.cell ⟨243, by decide⟩) = true := by
  kernel_decide

theorem certificate_243 :
    Certificate (table.cell ⟨243, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_243,
    crossing_of_check crossingCheck_243,
    scalar_of_check scalarCheck_243⟩

end Erdos1038.HighKPlatformConstantTableChunk243
