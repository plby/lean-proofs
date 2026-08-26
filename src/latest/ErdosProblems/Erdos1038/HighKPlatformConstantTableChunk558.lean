import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 558 through 558. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk558

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_558 :
    geometryCheck (table.cell ⟨558, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_558 :
    crossingCheck (table.cell ⟨558, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_558 :
    scalarCheck (table.cell ⟨558, by decide⟩) = true := by
  kernel_decide

theorem certificate_558 :
    Certificate (table.cell ⟨558, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_558,
    crossing_of_check crossingCheck_558,
    scalar_of_check scalarCheck_558⟩

end Erdos1038.HighKPlatformConstantTableChunk558
