import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 575 through 575. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk575

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_575 :
    geometryCheck (table.cell ⟨575, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_575 :
    crossingCheck (table.cell ⟨575, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_575 :
    scalarCheck (table.cell ⟨575, by decide⟩) = true := by
  kernel_decide

theorem certificate_575 :
    Certificate (table.cell ⟨575, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_575,
    crossing_of_check crossingCheck_575,
    scalar_of_check scalarCheck_575⟩

end Erdos1038.HighKPlatformConstantTableChunk575
