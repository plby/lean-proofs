import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 257 through 257. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk257

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_257 :
    geometryCheck (table.cell ⟨257, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_257 :
    crossingCheck (table.cell ⟨257, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_257 :
    scalarCheck (table.cell ⟨257, by decide⟩) = true := by
  kernel_decide

theorem certificate_257 :
    Certificate (table.cell ⟨257, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_257,
    crossing_of_check crossingCheck_257,
    scalar_of_check scalarCheck_257⟩

end Erdos1038.HighKPlatformConstantTableChunk257
