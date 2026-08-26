import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 359 through 359. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk359

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_359 :
    geometryCheck (table.cell ⟨359, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_359 :
    crossingCheck (table.cell ⟨359, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_359 :
    scalarCheck (table.cell ⟨359, by decide⟩) = true := by
  kernel_decide

theorem certificate_359 :
    Certificate (table.cell ⟨359, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_359,
    crossing_of_check crossingCheck_359,
    scalar_of_check scalarCheck_359⟩

end Erdos1038.HighKPlatformConstantTableChunk359
