import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 184 through 184. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk184

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_184 :
    geometryCheck (table.cell ⟨184, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_184 :
    crossingCheck (table.cell ⟨184, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_184 :
    scalarCheck (table.cell ⟨184, by decide⟩) = true := by
  kernel_decide

theorem certificate_184 :
    Certificate (table.cell ⟨184, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_184,
    crossing_of_check crossingCheck_184,
    scalar_of_check scalarCheck_184⟩

end Erdos1038.HighKPlatformConstantTableChunk184
