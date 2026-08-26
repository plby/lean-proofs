import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 192 through 192. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk192

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_192 :
    geometryCheck (table.cell ⟨192, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_192 :
    crossingCheck (table.cell ⟨192, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_192 :
    scalarCheck (table.cell ⟨192, by decide⟩) = true := by
  kernel_decide

theorem certificate_192 :
    Certificate (table.cell ⟨192, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_192,
    crossing_of_check crossingCheck_192,
    scalar_of_check scalarCheck_192⟩

end Erdos1038.HighKPlatformConstantTableChunk192
