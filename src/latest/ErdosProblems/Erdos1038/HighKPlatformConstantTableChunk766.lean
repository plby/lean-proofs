import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 766 through 766. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk766

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_766 :
    geometryCheck (table.cell ⟨766, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_766 :
    crossingCheck (table.cell ⟨766, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_766 :
    scalarCheck (table.cell ⟨766, by decide⟩) = true := by
  kernel_decide

theorem certificate_766 :
    Certificate (table.cell ⟨766, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_766,
    crossing_of_check crossingCheck_766,
    scalar_of_check scalarCheck_766⟩

end Erdos1038.HighKPlatformConstantTableChunk766
