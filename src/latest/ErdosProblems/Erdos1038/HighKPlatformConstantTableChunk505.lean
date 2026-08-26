import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 505 through 505. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk505

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_505 :
    geometryCheck (table.cell ⟨505, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_505 :
    crossingCheck (table.cell ⟨505, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_505 :
    scalarCheck (table.cell ⟨505, by decide⟩) = true := by
  kernel_decide

theorem certificate_505 :
    Certificate (table.cell ⟨505, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_505,
    crossing_of_check crossingCheck_505,
    scalar_of_check scalarCheck_505⟩

end Erdos1038.HighKPlatformConstantTableChunk505
