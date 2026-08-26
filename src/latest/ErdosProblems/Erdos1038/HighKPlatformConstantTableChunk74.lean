import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 74 through 74. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk74

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_074 :
    geometryCheck (table.cell ⟨74, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_074 :
    crossingCheck (table.cell ⟨74, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_074 :
    scalarCheck (table.cell ⟨74, by decide⟩) = true := by
  kernel_decide

theorem certificate_074 :
    Certificate (table.cell ⟨74, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_074,
    crossing_of_check crossingCheck_074,
    scalar_of_check scalarCheck_074⟩

end Erdos1038.HighKPlatformConstantTableChunk74
