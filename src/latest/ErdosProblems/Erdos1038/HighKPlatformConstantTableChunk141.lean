import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 141 through 141. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk141

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_141 :
    geometryCheck (table.cell ⟨141, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_141 :
    crossingCheck (table.cell ⟨141, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_141 :
    scalarCheck (table.cell ⟨141, by decide⟩) = true := by
  kernel_decide

theorem certificate_141 :
    Certificate (table.cell ⟨141, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_141,
    crossing_of_check crossingCheck_141,
    scalar_of_check scalarCheck_141⟩

end Erdos1038.HighKPlatformConstantTableChunk141
