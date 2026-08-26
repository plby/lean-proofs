import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 312 through 312. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk312

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_312 :
    geometryCheck (table.cell ⟨312, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_312 :
    crossingCheck (table.cell ⟨312, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_312 :
    scalarCheck (table.cell ⟨312, by decide⟩) = true := by
  kernel_decide

theorem certificate_312 :
    Certificate (table.cell ⟨312, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_312,
    crossing_of_check crossingCheck_312,
    scalar_of_check scalarCheck_312⟩

end Erdos1038.HighKPlatformConstantTableChunk312
