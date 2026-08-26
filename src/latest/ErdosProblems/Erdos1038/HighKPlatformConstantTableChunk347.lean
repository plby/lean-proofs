import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 347 through 347. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk347

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_347 :
    geometryCheck (table.cell ⟨347, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_347 :
    crossingCheck (table.cell ⟨347, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_347 :
    scalarCheck (table.cell ⟨347, by decide⟩) = true := by
  kernel_decide

theorem certificate_347 :
    Certificate (table.cell ⟨347, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_347,
    crossing_of_check crossingCheck_347,
    scalar_of_check scalarCheck_347⟩

end Erdos1038.HighKPlatformConstantTableChunk347
