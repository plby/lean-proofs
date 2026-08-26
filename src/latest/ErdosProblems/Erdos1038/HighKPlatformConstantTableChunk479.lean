import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 479 through 479. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk479

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_479 :
    geometryCheck (table.cell ⟨479, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_479 :
    crossingCheck (table.cell ⟨479, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_479 :
    scalarCheck (table.cell ⟨479, by decide⟩) = true := by
  kernel_decide

theorem certificate_479 :
    Certificate (table.cell ⟨479, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_479,
    crossing_of_check crossingCheck_479,
    scalar_of_check scalarCheck_479⟩

end Erdos1038.HighKPlatformConstantTableChunk479
