import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 729 through 729. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk729

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_729 :
    geometryCheck (table.cell ⟨729, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_729 :
    crossingCheck (table.cell ⟨729, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_729 :
    scalarCheck (table.cell ⟨729, by decide⟩) = true := by
  kernel_decide

theorem certificate_729 :
    Certificate (table.cell ⟨729, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_729,
    crossing_of_check crossingCheck_729,
    scalar_of_check scalarCheck_729⟩

end Erdos1038.HighKPlatformConstantTableChunk729
