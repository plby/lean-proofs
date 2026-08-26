import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 431 through 431. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk431

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_431 :
    geometryCheck (table.cell ⟨431, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_431 :
    crossingCheck (table.cell ⟨431, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_431 :
    scalarCheck (table.cell ⟨431, by decide⟩) = true := by
  kernel_decide

theorem certificate_431 :
    Certificate (table.cell ⟨431, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_431,
    crossing_of_check crossingCheck_431,
    scalar_of_check scalarCheck_431⟩

end Erdos1038.HighKPlatformConstantTableChunk431
