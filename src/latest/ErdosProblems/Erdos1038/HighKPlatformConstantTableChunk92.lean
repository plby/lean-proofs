import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 92 through 92. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk92

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_092 :
    geometryCheck (table.cell ⟨92, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_092 :
    crossingCheck (table.cell ⟨92, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_092 :
    scalarCheck (table.cell ⟨92, by decide⟩) = true := by
  kernel_decide

theorem certificate_092 :
    Certificate (table.cell ⟨92, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_092,
    crossing_of_check crossingCheck_092,
    scalar_of_check scalarCheck_092⟩

end Erdos1038.HighKPlatformConstantTableChunk92
