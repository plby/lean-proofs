import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 499 through 499. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk499

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_499 :
    geometryCheck (table.cell ⟨499, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_499 :
    crossingCheck (table.cell ⟨499, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_499 :
    scalarCheck (table.cell ⟨499, by decide⟩) = true := by
  kernel_decide

theorem certificate_499 :
    Certificate (table.cell ⟨499, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_499,
    crossing_of_check crossingCheck_499,
    scalar_of_check scalarCheck_499⟩

end Erdos1038.HighKPlatformConstantTableChunk499
