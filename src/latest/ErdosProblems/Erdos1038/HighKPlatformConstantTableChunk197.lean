import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 197 through 197. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk197

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_197 :
    geometryCheck (table.cell ⟨197, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_197 :
    crossingCheck (table.cell ⟨197, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_197 :
    scalarCheck (table.cell ⟨197, by decide⟩) = true := by
  kernel_decide

theorem certificate_197 :
    Certificate (table.cell ⟨197, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_197,
    crossing_of_check crossingCheck_197,
    scalar_of_check scalarCheck_197⟩

end Erdos1038.HighKPlatformConstantTableChunk197
