import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 406 through 406. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk406

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_406 :
    geometryCheck (table.cell ⟨406, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_406 :
    crossingCheck (table.cell ⟨406, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_406 :
    scalarCheck (table.cell ⟨406, by decide⟩) = true := by
  kernel_decide

theorem certificate_406 :
    Certificate (table.cell ⟨406, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_406,
    crossing_of_check crossingCheck_406,
    scalar_of_check scalarCheck_406⟩

end Erdos1038.HighKPlatformConstantTableChunk406
