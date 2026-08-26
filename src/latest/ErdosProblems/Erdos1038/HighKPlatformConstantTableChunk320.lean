import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 320 through 320. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk320

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_320 :
    geometryCheck (table.cell ⟨320, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_320 :
    crossingCheck (table.cell ⟨320, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_320 :
    scalarCheck (table.cell ⟨320, by decide⟩) = true := by
  kernel_decide

theorem certificate_320 :
    Certificate (table.cell ⟨320, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_320,
    crossing_of_check crossingCheck_320,
    scalar_of_check scalarCheck_320⟩

end Erdos1038.HighKPlatformConstantTableChunk320
