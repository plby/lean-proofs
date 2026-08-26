import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 436 through 436. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk436

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_436 :
    geometryCheck (table.cell ⟨436, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_436 :
    crossingCheck (table.cell ⟨436, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_436 :
    scalarCheck (table.cell ⟨436, by decide⟩) = true := by
  kernel_decide

theorem certificate_436 :
    Certificate (table.cell ⟨436, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_436,
    crossing_of_check crossingCheck_436,
    scalar_of_check scalarCheck_436⟩

end Erdos1038.HighKPlatformConstantTableChunk436
