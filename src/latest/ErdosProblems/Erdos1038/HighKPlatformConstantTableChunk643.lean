import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 643 through 643. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk643

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_643 :
    geometryCheck (table.cell ⟨643, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_643 :
    crossingCheck (table.cell ⟨643, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_643 :
    scalarCheck (table.cell ⟨643, by decide⟩) = true := by
  kernel_decide

theorem certificate_643 :
    Certificate (table.cell ⟨643, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_643,
    crossing_of_check crossingCheck_643,
    scalar_of_check scalarCheck_643⟩

end Erdos1038.HighKPlatformConstantTableChunk643
