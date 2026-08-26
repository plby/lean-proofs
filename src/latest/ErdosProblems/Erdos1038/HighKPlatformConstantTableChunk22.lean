import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 22 through 22. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk22

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_022 :
    geometryCheck (table.cell ⟨22, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_022 :
    crossingCheck (table.cell ⟨22, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_022 :
    scalarCheck (table.cell ⟨22, by decide⟩) = true := by
  kernel_decide

theorem certificate_022 :
    Certificate (table.cell ⟨22, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_022,
    crossing_of_check crossingCheck_022,
    scalar_of_check scalarCheck_022⟩

end Erdos1038.HighKPlatformConstantTableChunk22
