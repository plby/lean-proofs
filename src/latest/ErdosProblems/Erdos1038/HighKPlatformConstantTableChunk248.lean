import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 248 through 248. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk248

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_248 :
    geometryCheck (table.cell ⟨248, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_248 :
    crossingCheck (table.cell ⟨248, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_248 :
    scalarCheck (table.cell ⟨248, by decide⟩) = true := by
  kernel_decide

theorem certificate_248 :
    Certificate (table.cell ⟨248, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_248,
    crossing_of_check crossingCheck_248,
    scalar_of_check scalarCheck_248⟩

end Erdos1038.HighKPlatformConstantTableChunk248
