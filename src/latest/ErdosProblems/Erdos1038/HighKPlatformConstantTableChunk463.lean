import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 463 through 463. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk463

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_463 :
    geometryCheck (table.cell ⟨463, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_463 :
    crossingCheck (table.cell ⟨463, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_463 :
    scalarCheck (table.cell ⟨463, by decide⟩) = true := by
  kernel_decide

theorem certificate_463 :
    Certificate (table.cell ⟨463, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_463,
    crossing_of_check crossingCheck_463,
    scalar_of_check scalarCheck_463⟩

end Erdos1038.HighKPlatformConstantTableChunk463
