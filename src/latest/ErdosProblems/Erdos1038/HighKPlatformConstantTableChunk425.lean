import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 425 through 425. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk425

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_425 :
    geometryCheck (table.cell ⟨425, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_425 :
    crossingCheck (table.cell ⟨425, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_425 :
    scalarCheck (table.cell ⟨425, by decide⟩) = true := by
  kernel_decide

theorem certificate_425 :
    Certificate (table.cell ⟨425, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_425,
    crossing_of_check crossingCheck_425,
    scalar_of_check scalarCheck_425⟩

end Erdos1038.HighKPlatformConstantTableChunk425
