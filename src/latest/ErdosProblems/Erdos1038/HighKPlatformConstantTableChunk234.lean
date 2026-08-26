import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 234 through 234. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk234

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_234 :
    geometryCheck (table.cell ⟨234, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_234 :
    crossingCheck (table.cell ⟨234, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_234 :
    scalarCheck (table.cell ⟨234, by decide⟩) = true := by
  kernel_decide

theorem certificate_234 :
    Certificate (table.cell ⟨234, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_234,
    crossing_of_check crossingCheck_234,
    scalar_of_check scalarCheck_234⟩

end Erdos1038.HighKPlatformConstantTableChunk234
