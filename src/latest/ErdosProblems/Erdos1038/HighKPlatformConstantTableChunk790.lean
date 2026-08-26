import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 790 through 790. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk790

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_790 :
    geometryCheck (table.cell ⟨790, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_790 :
    crossingCheck (table.cell ⟨790, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_790 :
    scalarCheck (table.cell ⟨790, by decide⟩) = true := by
  kernel_decide

theorem certificate_790 :
    Certificate (table.cell ⟨790, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_790,
    crossing_of_check crossingCheck_790,
    scalar_of_check scalarCheck_790⟩

end Erdos1038.HighKPlatformConstantTableChunk790
