import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 222 through 222. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk222

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_222 :
    geometryCheck (table.cell ⟨222, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_222 :
    crossingCheck (table.cell ⟨222, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_222 :
    scalarCheck (table.cell ⟨222, by decide⟩) = true := by
  kernel_decide

theorem certificate_222 :
    Certificate (table.cell ⟨222, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_222,
    crossing_of_check crossingCheck_222,
    scalar_of_check scalarCheck_222⟩

end Erdos1038.HighKPlatformConstantTableChunk222
