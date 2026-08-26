import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 269 through 269. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk269

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_269 :
    geometryCheck (table.cell ⟨269, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_269 :
    crossingCheck (table.cell ⟨269, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_269 :
    scalarCheck (table.cell ⟨269, by decide⟩) = true := by
  kernel_decide

theorem certificate_269 :
    Certificate (table.cell ⟨269, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_269,
    crossing_of_check crossingCheck_269,
    scalar_of_check scalarCheck_269⟩

end Erdos1038.HighKPlatformConstantTableChunk269
