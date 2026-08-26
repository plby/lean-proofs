import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 682 through 682. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk682

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_682 :
    geometryCheck (table.cell ⟨682, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_682 :
    crossingCheck (table.cell ⟨682, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_682 :
    scalarCheck (table.cell ⟨682, by decide⟩) = true := by
  kernel_decide

theorem certificate_682 :
    Certificate (table.cell ⟨682, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_682,
    crossing_of_check crossingCheck_682,
    scalar_of_check scalarCheck_682⟩

end Erdos1038.HighKPlatformConstantTableChunk682
