import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 255 through 255. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk255

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_255 :
    geometryCheck (table.cell ⟨255, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_255 :
    crossingCheck (table.cell ⟨255, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_255 :
    scalarCheck (table.cell ⟨255, by decide⟩) = true := by
  kernel_decide

theorem certificate_255 :
    Certificate (table.cell ⟨255, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_255,
    crossing_of_check crossingCheck_255,
    scalar_of_check scalarCheck_255⟩

end Erdos1038.HighKPlatformConstantTableChunk255
