import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 94 through 94. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk94

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_094 :
    geometryCheck (table.cell ⟨94, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_094 :
    crossingCheck (table.cell ⟨94, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_094 :
    scalarCheck (table.cell ⟨94, by decide⟩) = true := by
  kernel_decide

theorem certificate_094 :
    Certificate (table.cell ⟨94, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_094,
    crossing_of_check crossingCheck_094,
    scalar_of_check scalarCheck_094⟩

end Erdos1038.HighKPlatformConstantTableChunk94
