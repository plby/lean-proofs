import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 181 through 181. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk181

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_181 :
    geometryCheck (table.cell ⟨181, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_181 :
    crossingCheck (table.cell ⟨181, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_181 :
    scalarCheck (table.cell ⟨181, by decide⟩) = true := by
  kernel_decide

theorem certificate_181 :
    Certificate (table.cell ⟨181, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_181,
    crossing_of_check crossingCheck_181,
    scalar_of_check scalarCheck_181⟩

end Erdos1038.HighKPlatformConstantTableChunk181
