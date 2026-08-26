import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 165 through 165. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk165

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_165 :
    geometryCheck (table.cell ⟨165, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_165 :
    crossingCheck (table.cell ⟨165, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_165 :
    scalarCheck (table.cell ⟨165, by decide⟩) = true := by
  kernel_decide

theorem certificate_165 :
    Certificate (table.cell ⟨165, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_165,
    crossing_of_check crossingCheck_165,
    scalar_of_check scalarCheck_165⟩

end Erdos1038.HighKPlatformConstantTableChunk165
