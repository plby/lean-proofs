import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 309 through 309. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk309

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_309 :
    geometryCheck (table.cell ⟨309, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_309 :
    crossingCheck (table.cell ⟨309, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_309 :
    scalarCheck (table.cell ⟨309, by decide⟩) = true := by
  kernel_decide

theorem certificate_309 :
    Certificate (table.cell ⟨309, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_309,
    crossing_of_check crossingCheck_309,
    scalar_of_check scalarCheck_309⟩

end Erdos1038.HighKPlatformConstantTableChunk309
