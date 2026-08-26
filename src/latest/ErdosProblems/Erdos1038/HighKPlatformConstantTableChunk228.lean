import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 228 through 228. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk228

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_228 :
    geometryCheck (table.cell ⟨228, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_228 :
    crossingCheck (table.cell ⟨228, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_228 :
    scalarCheck (table.cell ⟨228, by decide⟩) = true := by
  kernel_decide

theorem certificate_228 :
    Certificate (table.cell ⟨228, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_228,
    crossing_of_check crossingCheck_228,
    scalar_of_check scalarCheck_228⟩

end Erdos1038.HighKPlatformConstantTableChunk228
