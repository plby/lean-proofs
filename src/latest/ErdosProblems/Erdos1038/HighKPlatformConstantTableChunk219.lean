import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 219 through 219. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk219

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_219 :
    geometryCheck (table.cell ⟨219, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_219 :
    crossingCheck (table.cell ⟨219, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_219 :
    scalarCheck (table.cell ⟨219, by decide⟩) = true := by
  kernel_decide

theorem certificate_219 :
    Certificate (table.cell ⟨219, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_219,
    crossing_of_check crossingCheck_219,
    scalar_of_check scalarCheck_219⟩

end Erdos1038.HighKPlatformConstantTableChunk219
