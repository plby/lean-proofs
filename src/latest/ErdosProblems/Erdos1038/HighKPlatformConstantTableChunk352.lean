import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 352 through 352. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk352

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_352 :
    geometryCheck (table.cell ⟨352, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_352 :
    crossingCheck (table.cell ⟨352, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_352 :
    scalarCheck (table.cell ⟨352, by decide⟩) = true := by
  kernel_decide

theorem certificate_352 :
    Certificate (table.cell ⟨352, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_352,
    crossing_of_check crossingCheck_352,
    scalar_of_check scalarCheck_352⟩

end Erdos1038.HighKPlatformConstantTableChunk352
