import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 209 through 209. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk209

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_209 :
    geometryCheck (table.cell ⟨209, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_209 :
    crossingCheck (table.cell ⟨209, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_209 :
    scalarCheck (table.cell ⟨209, by decide⟩) = true := by
  kernel_decide

theorem certificate_209 :
    Certificate (table.cell ⟨209, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_209,
    crossing_of_check crossingCheck_209,
    scalar_of_check scalarCheck_209⟩

end Erdos1038.HighKPlatformConstantTableChunk209
